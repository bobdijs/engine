"""
6.176 MIT POKERBOTS GAME ENGINE
DO NOT REMOVE, RENAME, OR EDIT THIS FILE
"""
import json
import os
import socket
import subprocess
import sys
import time
from collections import namedtuple
from queue import Queue
from threading import Thread

import eval7

sys.path.append(os.getcwd())
from config import *

FoldAction = namedtuple('FoldAction', [])
CallAction = namedtuple('CallAction', [])
CheckAction = namedtuple('CheckAction', [])
# we coalesce BetAction and RaiseAction for convenience
RaiseAction = namedtuple('RaiseAction', ['amount'])
TerminalState = namedtuple('TerminalState', ['deltas', 'previous_state'])

STREET_NAMES = ['Flop', 'Turn', 'River']
DECODE = {'F': FoldAction, 'C': CallAction, 'K': CheckAction, 'R': RaiseAction}
CCARDS = lambda cards: ','.join(map(str, cards))
PCARDS = lambda cards: '[{}]'.format(' '.join(map(str, cards)))
PVALUE = lambda name, value: ', {} ({})'.format(name, value)
STATUS = lambda players: ''.join([PVALUE(p.name, p.bankroll) for p in players])


# Socket encoding scheme:
#
# T#.### the player's game clock
# P# the player's index
# H**,** the player's hand in common format
# F a fold action in the round history
# C a call action in the round history
# K a check action in the round history
# R### a raise action in the round history
# B**,**,**,**,** the board cards in common format
# O**,** the opponent's hand in common format
# D### the player's bankroll delta from the round
# Q game over
#
# Clauses are separated by spaces
# Messages end with '\n'
# The engine expects a response of K at the end of the round as an ack,
# otherwise a response which encodes the player's action
# Action history is sent once, including the player's actions


class RoundState(namedtuple('_RoundState', ['button', 'street', 'pips', 'stacks', 'pot', 'last_raiser', 'hands', 'deck',
                                            'previous_state'])):
    """
    Encodes the game tree for one round of poker.
    """

    def showdown(self):
        """
        Compares the players' hands and computes payoffs.
        """
        winners = []
        for i, hand in enumerate(self.hands):
            if hand is None:
                continue
            score = eval7.evaluate(self.deck.peek(5) + hand)
            if len(winners) == 0 or score > winners[0]:
                winners = [i]
            elif score == winners[0]:
                winners.append(i)
        winnings = []
        for i in range(len(self.hands)):
            winnings.append((self.pot / len(winners)) if i in winners else 0)

        return TerminalState(winnings, self)

    def legal_actions(self):
        """
        Returns a set which corresponds to the active player's legal moves.
        """
        active = self.button % len(self.stacks)
        max_pip = max([(0 if i is None else i) for i in self.pips])
        continue_cost = max_pip - self.pips[active]
        if continue_cost == 0:
            if self.player_can_afford(exceptions=[active]) and self.pips[active] != 0:
                return {CheckAction, RaiseAction}
            return {CheckAction}
        # continue_cost > 0
        # similarly, re-raising is only allowed if both players can afford it
        if self.player_can_afford(amount=continue_cost, exceptions=[active]) and self.pips[active] > continue_cost:
            return {FoldAction, CallAction, RaiseAction}
        return {FoldAction, CallAction}

    def raise_bounds(self):
        """
        Returns a tuple of the minimum and maximum legal raises.
        """
        active = self.button % len(self.stacks)
        continue_cost = max([(0 if i is None else i) for i in self.pips]) - self.pips[active]
        max_contribution = min(self.stacks[active], max([(0 if i is None else i) for i in self.stacks]) + continue_cost)
        min_contribution = min(max_contribution, continue_cost + max(continue_cost, BIG_BLIND))
        return self.pips[active] + min_contribution, self.pips[active] + max_contribution

    def proceed_street(self):
        """
        Resets the players' pips and advances the game tree to the next round of betting.
        """
        # TODO: Handle all-ins and side pots and turn self.pot into a list of pots
        for p in self.pips:
            self.pot += p

        if self.street == 5:
            return self.showdown()
        new_street = 3 if self.street == 0 else self.street + 1
        return RoundState(1, new_street, [(None if i is None else 0) for i in self.pips], self.stacks, self.pot,
                          None, self.hands, self.deck, self)

    def pass_round(self):
        return RoundState(self.button + 1, self.street, self.pips, self.stacks, self.pot, self.last_raiser,
                          self.hands, self.deck, self)

    def proceed(self, action):
        """
        Advances the game tree by one action performed by the active player.
        """
        active = self.button % len(self.stacks)
        last_raiser = active if self.last_raiser is None else self.last_raiser

        if isinstance(action, FoldAction):
            active_players = self.fold(active)
            if len(active_players) == 1:
                return TerminalState([], self)  # TODO: Create a better terminal state
            elif last_raiser == self.button + 1:
                return self.proceed_street()
            return RoundState(self.button + 1, self.street, self.pips, self.stacks, self.pot, last_raiser,
                              self.hands, self.deck, self)
        if isinstance(action, CallAction):
            # both players acted
            new_pips = list(self.pips)
            new_stacks = list(self.stacks)
            to_call = 0
            for p in self.pips:
                to_call = max(p, to_call)
            # At max it can call all-in
            to_call = min(new_stacks[active], to_call)
            new_stacks[active] -= to_call
            new_pips[active] += to_call
            if last_raiser - 1 == active:
                return self.proceed_street()
            return RoundState(self.button + 1, self.street, new_pips, new_stacks, self.pot, last_raiser,
                              self.hands, self.deck, self)
        if isinstance(action, CheckAction):
            if last_raiser - 1 == active:
                return self.proceed_street()
            # let opponent act
            return RoundState(self.button + 1, self.street, self.pips, self.stacks, self.pot, last_raiser,
                              self.hands, self.deck, self)
        # isinstance(action, RaiseAction)
        new_pips = list(self.pips)
        new_stacks = list(self.stacks)
        contribution = min(action.amount - new_pips[active], new_stacks[active])
        new_stacks[active] -= contribution
        new_pips[active] += contribution
        return RoundState(self.button + 1, self.street, new_pips, new_stacks, self.pot, active, self.hands,
                          self.deck, self)

    def player_can_afford(self, amount=1, exceptions=None):
        # we can only raise the stakes if active and any other player can afford it.
        if exceptions is None:
            exceptions = []
        for i, p in enumerate(self.pips):
            if i not in exceptions and p is not None and p >= amount:
                return True
        return False

    def fold(self, player):
        """
        Folds the player with the given id.
        And returns the list of ids for players that are still active.
        """
        self.stacks[player] = None
        self.hands[player] = None
        self.pips[player] = None
        active_players = []
        for i, s in enumerate(self.stacks):
            if s is not None:
                active_players.append(i)
        return active_players


class Player():
    """
    Handles subprocess and socket interactions with one player's pokerbot.
    """

    def __init__(self, name, path):
        self.name = name
        self.path = path
        self.game_clock = STARTING_GAME_CLOCK
        self.bankroll = 0
        self.commands = None
        self.bot_subprocess = None
        self.socketfile = None
        self.bytes_queue = Queue()

    def build(self):
        """
        Loads the commands file and builds the pokerbot.
        """
        try:
            with open(self.path + '/commands.json', 'r') as json_file:
                commands = json.load(json_file)
            if ('build' in commands and 'run' in commands and
                    isinstance(commands['build'], list) and
                    isinstance(commands['run'], list)):
                self.commands = commands
            else:
                print(self.name, 'commands.json missing command')
        except FileNotFoundError:
            print(self.name, 'commands.json not found - check PLAYER_PATH')
        except json.decoder.JSONDecodeError:
            print(self.name, 'commands.json misformatted')
        if self.commands is not None and len(self.commands['build']) > 0:
            try:
                proc = subprocess.run(self.commands['build'],
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                      cwd=self.path, timeout=BUILD_TIMEOUT, check=False)
                self.bytes_queue.put(proc.stdout)
            except subprocess.TimeoutExpired as timeout_expired:
                error_message = 'Timed out waiting for ' + self.name + ' to build'
                print(error_message)
                self.bytes_queue.put(timeout_expired.stdout)
                self.bytes_queue.put(error_message.encode())
            except (TypeError, ValueError):
                print(self.name, 'build command misformatted')
            except OSError:
                print(self.name, 'build failed - check "build" in commands.json')

    def run(self):
        """
        Runs the pokerbot and establishes the socket connection.
        """
        if self.commands is not None and len(self.commands['run']) > 0:
            try:
                server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                with server_socket:
                    server_socket.bind(('', 0))
                    server_socket.settimeout(CONNECT_TIMEOUT)
                    server_socket.listen()
                    port = server_socket.getsockname()[1]
                    proc = subprocess.Popen(self.commands['run'] + [str(port)],
                                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                            cwd=self.path)
                    self.bot_subprocess = proc

                    # function for bot listening
                    def enqueue_output(out, queue):
                        try:
                            for line in out:
                                queue.put(line)
                        except ValueError:
                            pass

                    # start a separate bot listening thread which dies with the program
                    Thread(target=enqueue_output, args=(proc.stdout, self.bytes_queue), daemon=True).start()
                    # block until we timeout or the player connects
                    client_socket, _ = server_socket.accept()
                    with client_socket:
                        client_socket.settimeout(CONNECT_TIMEOUT)
                        sock = client_socket.makefile('rw')
                        self.socketfile = sock
                        print(self.name, 'connected successfully')
            except (TypeError, ValueError):
                print(self.name, 'run command misformatted')
            except OSError:
                print(self.name, 'run failed - check "run" in commands.json')
            except socket.timeout:
                print('Timed out waiting for', self.name, 'to connect')

    def stop(self):
        """
        Closes the socket connection and stops the pokerbot.
        """
        if self.socketfile is not None:
            try:
                self.socketfile.write('Q\n')
                self.socketfile.close()
            except socket.timeout:
                print('Timed out waiting for', self.name, 'to disconnect')
            except OSError:
                print('Could not close socket connection with', self.name)
        if self.bot_subprocess is not None:
            try:
                outs, _ = self.bot_subprocess.communicate(timeout=CONNECT_TIMEOUT)
                self.bytes_queue.put(outs)
            except subprocess.TimeoutExpired:
                print('Timed out waiting for', self.name, 'to quit')
                self.bot_subprocess.kill()
                outs, _ = self.bot_subprocess.communicate()
                self.bytes_queue.put(outs)
        with open(self.name + '.txt', 'wb') as log_file:
            bytes_written = 0
            for output in self.bytes_queue.queue:
                try:
                    bytes_written += log_file.write(output)
                    if bytes_written >= PLAYER_LOG_SIZE_LIMIT:
                        break
                except TypeError:
                    pass

    def query(self, round_state, player_message, game_log):
        """
        Requests one action from the pokerbot over the socket connection.
        At the end of the round, we request a CheckAction from the pokerbot.
        """
        legal_actions = round_state.legal_actions() if isinstance(round_state, RoundState) else {CheckAction}
        if self.socketfile is not None and self.game_clock > 0.:
            try:
                player_message[0] = 'T{:.3f}'.format(self.game_clock)
                message = ' '.join(player_message) + '\n'
                del player_message[1:]  # do not send redundant action history
                start_time = time.perf_counter()
                self.socketfile.write(message)
                self.socketfile.flush()
                clause = self.socketfile.readline().strip()
                end_time = time.perf_counter()
                if ENFORCE_GAME_CLOCK:
                    self.game_clock -= end_time - start_time
                if self.game_clock <= 0.:
                    raise socket.timeout
                action = DECODE[clause[0]]
                if action in legal_actions:
                    if clause[0] == 'R':
                        amount = int(clause[1:])
                        min_raise, max_raise = round_state.raise_bounds()
                        if min_raise <= amount <= max_raise:
                            return action(amount)
                    else:
                        return action()
                game_log.append(self.name + ' attempted illegal ' + action.__name__)
            except socket.timeout:
                error_message = self.name + ' ran out of time'
                game_log.append(error_message)
                print(error_message)
                self.game_clock = 0.
            except OSError:
                error_message = self.name + ' disconnected'
                game_log.append(error_message)
                print(error_message)
                self.game_clock = 0.
            except (IndexError, KeyError, ValueError):
                game_log.append(self.name + ' response misformatted')
        return CheckAction() if CheckAction in legal_actions else FoldAction()


class Game():
    """
    Manages logging and the high-level game procedure.
    """

    def __init__(self):
        if len(PLAYERS_CONFIG) > 23:
            raise Exception("U Serious? There aren't enough cards in a deck.")
        players_str = ''
        self.player_messages = []
        for i, player in enumerate(PLAYERS_CONFIG):
            players_str += " " + player["name"] + (" vs" if i != len(PLAYERS_CONFIG) - 1 else "")
            self.player_messages.append([])

        self.log = ['6.176 MIT Pokerbots -' + players_str]

    def log_round_state(self, players, round_state):
        """
        Incorporates RoundState information into the game log and player messages.
        """
        if round_state.street == 0 and round_state.button == 0:
            self.log.append('{} posts the blind of {}'.format(players[0].name, SMALL_BLIND))
            self.log.append('{} posts the blind of {}'.format(players[1].name, BIG_BLIND))
            for i in range(len(round_state.hands)):
                self.log.append('{} dealt {}'.format(players[i].name, PCARDS(round_state.hands[i])))
                self.player_messages[i] = ['T0.', 'P0', 'H' + CCARDS(round_state.hands[i])]
        elif round_state.street > 0 and round_state.button == 1:
            board = round_state.deck.peek(round_state.street)
            compressed_board = 'B' + CCARDS(board)
            logstr = STREET_NAMES[round_state.street - 3] + ' ' + PCARDS(board)

            for i in range(len(players)):
                logstr += PVALUE(players[i].name, STARTING_STACK - round_state.stacks[i])
                self.player_messages[i].append(compressed_board)
            self.log.append(logstr)

    def log_action(self, name, action, bet_override):
        """
        Incorporates action information into the game log and player messages.
        """
        if isinstance(action, FoldAction):
            phrasing = ' folds'
            code = 'F'
        elif isinstance(action, CallAction):
            phrasing = ' calls'
            code = 'C'
        elif isinstance(action, CheckAction):
            phrasing = ' checks'
            code = 'K'
        else:  # isinstance(action, RaiseAction)
            phrasing = (' bets ' if bet_override else ' raises to ') + str(action.amount)
            code = 'R' + str(action.amount)
        self.log.append(name + phrasing)
        for m in self.player_messages:
            m.append(code)

    def log_terminal_state(self, players, round_state):
        """
        Incorporates TerminalState information into the game log and player messages.
        """
        previous_state = round_state.previous_state
        if FoldAction not in previous_state.legal_actions():
            self.log.append('{} shows {}'.format(players[0].name, PCARDS(previous_state.hands[0])))
            self.log.append('{} shows {}'.format(players[1].name, PCARDS(previous_state.hands[1])))
            self.player_messages[0].append('O' + CCARDS(previous_state.hands[1]))
            self.player_messages[1].append('O' + CCARDS(previous_state.hands[0]))
        self.log.append('{} awarded {}'.format(players[0].name, round_state.deltas[0]))
        self.log.append('{} awarded {}'.format(players[1].name, round_state.deltas[1]))
        self.player_messages[0].append('D' + str(round_state.deltas[0]))
        self.player_messages[1].append('D' + str(round_state.deltas[1]))

    def run_round(self, players):
        """
        Runs one round of poker.
        """
        deck = eval7.Deck()
        deck.shuffle()
        hands = [deck.deal(2) for _ in players]
        pips = [ANTE for _ in players]
        stacks = [STARTING_STACK for _ in players]
        pips[0] += SMALL_BLIND
        pips[1] += BIG_BLIND
        stacks[0] -= SMALL_BLIND
        stacks[1] -= BIG_BLIND
        pot = ANTE * len(players) + SMALL_BLIND + BIG_BLIND
        round_state = RoundState(3, 0, pips, stacks, pot, None, hands, deck, None)
        while not isinstance(round_state, TerminalState):
            self.log_round_state(players, round_state)
            active = round_state.button % len(players)
            if round_state.hands[active] is None:
                round_state = round_state.pass_round()
                continue
            player = players[active]
            action = player.query(round_state, self.player_messages[active], self.log)
            bet_override = (round_state.pips == [0, 0])
            self.log_action(player.name, action, bet_override)
            round_state = round_state.proceed(action)
        # self.log_terminal_state(players, round_state)
        for player, player_message, delta in zip(players, self.player_messages, round_state.deltas):
            player.query(round_state, player_message, self.log)
            player.bankroll += delta

    def run(self):
        """
        Runs one game of poker.
        """
        print('   __  _____________  ___       __           __        __    ')
        print('  /  |/  /  _/_  __/ / _ \\___  / /_____ ____/ /  ___  / /____')
        print(' / /|_/ // /  / /   / ___/ _ \\/  \'_/ -_) __/ _ \\/ _ \\/ __(_-<')
        print('/_/  /_/___/ /_/   /_/   \\___/_/\\_\\\\__/_/ /_.__/\\___/\\__/___/')
        print()
        print('Starting the Pokerbots engine...')
        players = []
        for p in PLAYERS_CONFIG:
            player = Player(p["name"], p["path"])
            players.append(player)
            player.build()
            player.run()
        for round_num in range(1, NUM_ROUNDS + 1):
            self.log.append('')
            self.log.append('Round #' + str(round_num) + STATUS(players))
            self.run_round(players)
            players = players[::-1]
        self.log.append('')
        self.log.append('Final' + STATUS(players))
        for player in players:
            player.stop()
        name = GAME_LOG_FILENAME + '.txt'
        print('Writing', name)
        with open(name, 'w') as log_file:
            log_file.write('\n'.join(self.log))


if __name__ == '__main__':
    Game().run()
