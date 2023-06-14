#####
# Finite State Automata in Python
# Coded by Ash DeClerk (declerk.gary@huskers.unl.edu) for use in their Prefix-Knuth-Bendix program
# Last updated 9/18/2022
#####



import copy
import random
from dataclasses import dataclass

class AlphabetError(Exception):
    """
    Exception raised when alphabets don't match.
    """

    def __init__(self, alph1, alph2, message):
        self.alph1 = alph1
        self.alph2 = alph2
        self.message = message



# The (determinisitic) FSA class. It's essentially a dictionary of lists as the transition function, a list of accept states, an int for number of states, a list of letters. By default, initial state is 0 and default target state is 0.
class FSA:

    def __init__(self, states, accepts, alphabet, transitions):
        # Initialization. I don't have any validity testing yet. That's probably worth doing in the final draft, but I don't care enough right now.
        self.states = states
        self.accepts = copy.deepcopy(accepts)
        self.alphabet = set(copy.deepcopy(alphabet))
        self.transitions = copy.deepcopy(transitions)

    def __repr__(self):
        # This is gonna just be annoyingly long, because it's nonsense otherwise.
        out = "Number of states: " + str(self.states) + "\n"
        out += "Accepting states: " + str(self.accepts) + "\n"
        out += "Alphabet: " + str(self.alphabet) + "\n"
        out += "Transitions: \n"
        for letter in self.transitions:
            # Note that this was originally sorted(self.transitions); that gave a type error, because None can't be compared to strings.
            out += "\t " + str(letter) + ": " + str(self.transitions[letter]) + "\n"
        return out

    def accepted(self, word):
        # word should be a list of elements from self.alphabet
        location = 0
        for letter in word:
            location = self.transitions[letter][location]
        if location in self.accepts:
            return True
        return False

    def addLetter(self, letter):
        # letter needs to be immutable, but that's really it.
        if letter not in self.alphabet:
            self.alphabet.update({letter})
            self.transitions[letter] = [0] * self.states

    def remLetter(self, letter):
        if letter in self.alphabet:
            self.alphabet.difference_update({letter})
            del self.transitions[letter]

    def addState(self):
        self.states += 1
        for letter in self.alphabet:
            self.transitions[letter].append(0)

    def remState(self, index):
        # This one's harder. We want to remove the state currently labeled by index, then renumber as appropriate in the transition function.
        if index <= self.states:
            self.states -= 1
            for letter in self.alphabet:
                del self.transitions[letter][index]
                for i in range(0, self.states):
                    if self.transitions[letter][i] > index:
                        self.transitions[letter][i] -= 1

    def changeEdge(self, start, end, label):
        self.transitions[label][start] = end

    def changeInit(self, index):
        # We're just gonna swap state 0 and state index
        # Deal with accepts
        if index in self.accepts:
            if 0 in self.accepts:
                pass
            else:
                self.accepts.difference_update({index})
                self.accepts.update({0})
        else:
            if 0 in self.accepts:
                self.accepts.difference_update({0})
                self.accepts.update({index})
        # Deal with transitions
        for letter in self.alphabet:
            self.transitions[letter][0], self.transitions[letter][index] = self.transitions[letter][index], self.transitions[letter][0]
            for state in range(0, self.states):
                if self.transitions[letter][state] == 0:
                    self.transitions[letter][state] = index
                elif self.transitions[letter][state] == index:
                    self.transitions[letter][state] = 0


@dataclass(frozen = True)
class frozenFSA:

    states: int
    accepts: frozenset
    alphabet: frozenset
    transitions: frozenset


def freeze(fsa):
    transitions = {}
    for key, item in fsa.transitions.items():
        transitions[key] = tuple(item)
    transitions = frozenset(transitions.items())
    return frozenFSA(states = fsa.states, accepts = frozenset(fsa.accepts), alphabet = frozenset(fsa.alphabet), transitions = transitions)

    
def complement(fsa):
    # No chance for alphabet errors here.
    acc = set(range(fsa.states))
    acc.difference_update(fsa.accepts)
    return FSA(fsa.states, acc, fsa.alphabet, fsa.transitions)


def product(fsa1, fsa2):
    # No chance for alphabet errors here.
    # Number of states: We need to have (fsa1.states + 1) * (fsa2.states + 1); the +1s are for eowacc x state (and vice versa), -1 for eow x eow, +1 for failure by eow
    states = (fsa1.states + 1) * (fsa2.states + 1)
    # The obvious way to view our states is as an array, so the ((fsa2.states + 2) * i + j)th state corresponds to state i in fsa1, state j in fsa2
    # state x eow should be i * (fsa2.states + 2) + fsa2.states + 1
    # eow x state should be (fsa1.states + 1) * (fsa2.states + 2) + j
    # Accept states: These are the states ((fsa2.states + 2) * i + j) where both states i and j are accept in the relevant fsas, or are eowacc
    accepts = set()
    for i in fsa1.accepts:
        for j in fsa2.accepts:
            accepts.update({i * (fsa2.states + 1) + j})
        accepts.update({(i + 1) * (fsa2.states + 1) - 1}) # This grabs state x eowacc
    for j in fsa2.accepts:
        accepts.update({(fsa1.states) * (fsa2.states + 1) + j}) # This grabs eowacc x state
    # Alphabet: We'll use tuples as our basic elements, with None standing in for "end of word".
    # This is where things get a bit funky, in order to make projection work the way we want it to.
    # Basically, we need our letters to be tuples. But if a letter is already a tuple (because we're producting where one fsa is a product), we should just extend the tuple.
    # And if both fsas are products, then we need to have even more fun.
    # So, first: We grab the arity of both fsas. I don't want to store arity information with the fsa, so we're gonna figure it out ourselves.
    arity1 = copy.deepcopy(fsa1.alphabet)
    arity1 = arity1.pop()
    if type(arity1) == tuple:
        arity1 = len(arity1)
    else:
        arity1 = 1
    arity2 = copy.deepcopy(fsa2.alphabet)
    arity2 = arity2.pop()
    if type(arity2) == tuple:
        arity2 = len(arity2)
    else:
        arity2 = 1
    alphabet = set()
    # Transitions: Annoying but straightforward.
    transitions = {}
    for let1 in fsa1.alphabet:
        for let2 in fsa2.alphabet:
            if type(let1) == tuple:
                list1 = list(let1)
            else:
                list1 = [let1]
            if type(let2) == tuple:
                list1.extend(let2)
            else:
                list1 += [let2]
            lettuple = tuple(list1)
            alphabet.update({lettuple})
            transitions[lettuple] = [states - 1] * states # initialize transition list
            for i in range(0, fsa1.states):
                for j in range(0, fsa2.states):
                    transitions[lettuple][i * (fsa2.states + 1) + j] = fsa1.transitions[let1][i] * (fsa2.states + 1) + fsa2.transitions[let2][j] # transitions for state x state
            # transitions for eow x state and state x eow default to the final state, which is guaranteed fail
        if type(let1) == tuple:
            list1 = list(let1)
        else:
            list1 = [let1]
        list1.extend([None] * arity2)
        lettuple = tuple(list1)
        alphabet.update({lettuple})
        transitions[lettuple] = [states - 1] * states
        for i in range(0, fsa1.states):
            for j in fsa2.accepts:
                transitions[lettuple][i * (fsa2.states + 1) + j] = (fsa1.transitions[let1][i] + 1) * (fsa2.states + 1) - 1 # transitions for state x state
            # transitions for eow x state fail
            transitions[lettuple][(i + 1) * (fsa2.states + 1) - 1] = (fsa1.transitions[let1][i] + 1) * (fsa2.states + 1) - 1 # transitions for state x eow 
    for let2 in fsa2.alphabet:
        list1 = [None] * arity1
        if type(let2) == tuple:
            list1.extend(let2)
        else:
            list1.append(let2)
        lettuple = tuple(list1)
        alphabet.update({lettuple})
        transitions[lettuple] = [states - 1] * states
        for i in fsa1.accepts:
            for j in range(0, fsa2.states):
                transitions[lettuple][i * (fsa2.states + 1) + j] = (fsa1.states) * (fsa2.states + 1) + fsa2.transitions[let2][j] # transitions for state x state
        # transitions for state x eow should fail
        for j in range(0, fsa2.states):
            transitions[lettuple][(fsa1.states) * (fsa2.states + 1) + j] = (fsa1.states) * (fsa2.states + 1) + fsa2.transitions[let2][j] # transitions for eow x state
    return FSA(states, accepts, alphabet, transitions)


def singFSA(alph, word):
    # An alphabet error can happen if word is not a word over alph.
    for let in word:
        if let not in alph:
            raise AlphabetError(alph, alph, "In singFSA, " + str(word) + " was not a word over " + str(alph))
    # The idea here is to have a state for each letter in the word, with a transition function that goes from one state to the next only on the appropriate letter.
    states = len(word) + 2
    alphabet = alph
    transitions = {}
    for let in alphabet:
        transitions[let] = [states - 1] * (states)
    for index in range(0, len(word)):
        transitions[word[index]][index] = index + 1
    accepts = {states - 2}
    return FSA(states, accepts, alphabet, transitions)

def emptyFSA(alph):
    # No chance for alphabet errors here.
    states = 1
    alphabet = alph
    transitions = {}
    for let in alphabet:
        transitions[let] = [0]
    accepts = set()
    return FSA(states, accepts, alphabet, transitions)

def allFSA(alph):
    # No chance for alphabet errors here.
    states = 1
    alphabet = alph
    transitions = {}
    for let in alphabet:
        transitions[let] = [0]
    accepts = {0}
    return FSA(states, accepts, alphabet, transitions)

def listInt(list1, list2):
    # It's useful to have the intersection of two lists for BFS
    out = []
    for entry in list1:
        if entry in list2:
            out.append(entry)
    return out

def listSub(list1, list2):
    # It's also useful to have the difference of two lists.
    out = []
    for entry in list1:
        if entry not in list2:
            out.append(entry)
    return out

def BFS(fsa):
    # Tested and working
    # First step: Minimize using Moore's algorithm.
    alphabet = fsa.alphabet
    # We can't sort alphabet, because 1) it might be a tuple rather than a list, and 2) None can't be compared to anything.
    P = []
    W = []
    if len(fsa.accepts) > 0:
        P.append(fsa.accepts)
        W.append(fsa.accepts)
    nonAcc = set(range(0, fsa.states)).difference(fsa.accepts)
    if len(nonAcc) > 0:
        P.append(nonAcc)
        W.append(nonAcc)
    del nonAcc
    while len(W) > 0:
        A = W.pop(0)
        for let in alphabet:
            X = []
            for state in range(0, fsa.states):
                # X = states s with s * let in A
                if fsa.transitions[let][state] in A:
                    X.append(state)
            for Y in P:
                if len(listInt(Y, X)) > 0 and len(listSub(Y, X)) > 0:
                    P.remove(Y)
                    P.append(listInt(Y, X))
                    P.append(listSub(Y, X))
                    if W.count(Y) > 0:
                        W.remove(Y)
                        W.append(listInt(Y, X))
                        W.append(listSub(Y, X))
                    else:
                        W.append(listInt(Y, X))
    # All of the stuff above just gets us P, which is the Myhill-Nerode equivalence classes;
    # We still need to work out transition function and accept stuff.
    # And making sure that we have the right initial state.
    # Then, of course, we still need to convert to BFS
    states = len(P)
    accepts = set()
    transitions = {}
    for let in alphabet:
        transitions[let] = [0] * (states)
    # Set the right initial state
    for i in range(0, len(P)):
        if 0 in P[i]:
            P.insert(0, P.pop(i))
    for i in range(0, len(P)):
        # Deal with accept stuff.
        if list(P[i])[0] in fsa.accepts:
            accepts.update({i})
        # Deal with transition stuff
        for let in alphabet:
            for j in range(0, len(P)):
                if fsa.transitions[let][list(P[i])[0]] in P[j]:
                    transitions[let][i] = j
    # And at this point, we have all the info for a minimized FSA
    # Which leaves conversion to BFS
    relabeling = {0: 0}
    unrelabeling = {0: 0}
    location = 0
    counter = 1
    newStates = states
    while counter <= len(P):
        for let in alphabet:
            if transitions[let][location] not in relabeling:
                relabeling[transitions[let][location]] = counter
                unrelabeling[counter] = transitions[let][location]
                counter += 1
        location = relabeling[location] + 1
        if location >= counter:
            newStates = counter
            break
        location = unrelabeling[location]
    # Now we need to relabel accepts and transitions
    newAccepts = set()
    for state in accepts:
        if state in relabeling.keys():
            newAccepts.update({relabeling[state]})
    newTransitions = {}
    for let in alphabet:
        newTransitions[let] = [0] * (newStates)
        for state in range(0, states):
            if state in relabeling.keys():
                newTransitions[let][relabeling[state]] = relabeling[transitions[let][state]]
    return FSA(newStates, newAccepts, alphabet, newTransitions)



# A nondeterministic class, because that will hopefully simplify several things
class NFA:

    def __init__(self, states, accepts, alphabet, transitions):
        # Initialization. I don't have any validity testing yet. That's probably worth doing in the final draft, but I don't care enough right now.
        # states is specifically non-fail states, btw.
        # TODO: validity testing
        self.states = states
        self.accepts = copy.deepcopy(accepts)
        self.alphabet = copy.deepcopy(alphabet)
        self.transitions = copy.deepcopy(transitions)

    def __repr__(self):
        # This is gonna just be annoyingly long, because it's nonsense otherwise.
        out = "Number of states: " + str(self.states) + "\n"
        out += "Accepting states: " + str(self.accepts) + "\n"
        out += "Alphabet: " + str(self.alphabet) + "\n"
        out += "Transitions: \n"
        for letter in self.transitions:
            out += "\t " + str(letter) + ": " + str(self.transitions[letter]) + "\n"
        return out

    def accepted(self, word):
        # word should be a list of elements from self.alphabet
        locations = {0}
        bread = {0}
        while bread != set():
            newBread = set()
            for state in bread:
                newBread.update(self.transitions[None][state])
            locations.update(newBread)
            bread = newBread
        for letter in word:
            newLocations = set()
            for state in locations:
                newLocations.update(self.transitions[letter][state])
            bread = newLocations
            while bread != set():
                newBread = set()
                for state in bread:
                    newBread.update(self.transitions[None][state])
                newlocations.update(newBread)
                bread = newBread
            locations = newLocations
        for state in locations:
            if self.accepts.count(state) > 0:
                return True
        return False

    def addLetter(self, letter):
        # letter needs to be immutable, but that's really it.
        # TODO: validity testing
        if letter not in self.alphabet:
            self.alphabet.update({letter})
            self.transitions[letter] = []
            for state in range(self.states):
                self.transitions[letter].append(set())

    def remLetter(self, letter):
        # TODO: validity testing?
        if letter in self.alphabet:
            self.alphabet.difference_update({letter})
            del self.transitions[letter]

    def addState(self):
        self.states += 1
        for letter in self.alphabet:
            self.transitions[letter].append(set())
        self.transitions[None].append(set())

    def remState(self, index):
        # This one's harder. We want to remove the state currently labeled by index, then renumber as appropriate in the transition function.
        # TODO: validity testing?
        if index <= self.states:
            self.states -= 1
            newAccepts = set()
            for state in self.accepts:
                if state < index:
                    newAccepts.update({state})
                if state > index:
                    newAccepts.update({state - 1})
            self.accepts = newAccepts
            for letter in self.alphabet:
                del self.transitions[letter][index]
                for i in range(0, self.states):
                    oldStates = self.transitions[letter][index].intersection(set(range(index + 1, self.states + 1)))
                    newStates = set()
                    for location in oldStates:
                        newStates.update(location - 1)
                    self.transitions[letter][index].intersection_update(set(range(0, index)))
                    self.transitions[letter][index].union_update(newStates)
            del self.transitions[None][index]
            for i in range(0, self.states):
                oldStates = self.transitions[letter][index].intersection(set(range(index + 1, self.states + 1)))
                newStates = set()
                for location in oldStates:
                    newStates.update(location - 1)
                self.transitions[letter][index].intersection_update(set(range(0, index)))
                self.transitions[letter][index].union_update(newStates)


    def addEdge(self, start, end, label):
        # TODO: validity testing
        self.transitions[label][start].update({end})

    def remEdge(self, start, end, label):
        # TODO: validity testing
        self.transitions[label][state].difference_update({end})

def nondeterminize(fsa):
    # Tested and working.
    states = fsa.states
    accepts = fsa.accepts
    alphabet = fsa.alphabet
    transitions = {}
    transitions[None] = [set()] * states
    for letter in alphabet:
        transitions[letter] = [set()] * states
        for state in range(0, states):
            transitions[letter][state] = set([fsa.transitions[letter][state]])
    return NFA(states, accepts, alphabet, transitions)

def determinize(nfa):
    # The naive approach (using power sets) doesn't work well because of memory issues. So we're gonna do this as a breadth-first search instead.
    alphabet = nfa.alphabet
    accepts = set()
    transitions = {}
    for let in alphabet:
        transitions[let] = [0]
    currentState = 0
    stateCount = 1
    start = {0}
    bread = {0}
    while bread != set():
        newBread = set()
        for state in bread:
            newBread.update(nfa.transitions[None][state])
        start.update(newBread)
        bread = newBread
    stateLabels = {0: tuple(start)}
    labelStates = {tuple(start): 0}
    for i in start:
        if i in nfa.accepts:
            accepts.update({0})
    # Basically what we're doing is similar to the relabeling algorithm in BFS.
    # That should leave us with just the accessible states, which will (hopefully) mean that we don't run out of memory.
    while True:
        for let in alphabet:
            # We need to grab all of the states that it would transition to.
            targets = set()
            accepting = False
            for source in stateLabels[currentState]:
                targets.update(nfa.transitions[let][source])
            if targets.intersection(set(nfa.accepts)) != set():
                accepting = True
            bread = targets
            while bread != set():
                newBread = set()
                for state in bread:
                    newBread.update(nfa.transitions[None][state])
                targets.update(newBread)
                bread = newBread
            targets = tuple(targets)
            if targets not in labelStates:
                labelStates[targets] = stateCount
                stateLabels[stateCount] = targets
                transitions[let][currentState] = stateCount
                if accepting:
                    accepts.update({stateCount})
                stateCount += 1
                for let in alphabet:
                    transitions[let].append(0)
            else:
                transitions[let][currentState] = labelStates[targets]
        currentState += 1
        if currentState >= stateCount:
            break
    out = FSA(stateCount, accepts, alphabet, transitions)
    return out

def star(fsa):
    out = nondeterminize(fsa)
    out.accepts.update({0})
    for letter in out.alphabet:
        for state in fsa.accepts:
            out.transitions[letter][state].update(out.transitions[letter][0])
    out = determinize(out)
    return out

def union(fsa1, fsa2):
    if fsa1.states == 1:
        if len(fsa1.accepts) == 1:
            return fsa1
        if len(fsa1.accepts) == 0:
            return fsa2
    if fsa2.states == 1:
        if len(fsa2.accepts) == 1:
            return fsa2
        if len(fsa2.accepts) == 0:
            return fsa1
    # There can be an alphabet error if fsa1 and fsa2 have different alphabets.
    if fsa1.alphabet != fsa2.alphabet:
        raise AlphabetError(fsa1.alphabet, fsa2.alphabet, "In union, " + str(fsa1) + " and " + str(fsa2) + " have different alphabets.")
    nfa1 = nondeterminize(fsa1)
    nfa2 = nondeterminize(fsa2)
    # The easy way to do this is to append states from nfa2 onto nfa1, along with a new 0
    for state in range(0, nfa2.states + 1):
        nfa1.addState()
    # then add the appropriate accept states
    if 0 in fsa1.accepts:
        nfa1.accepts.update({fsa1.states + fsa2.states})
    elif 0 in fsa2.accepts:
        nfa1.accepts.update({0})
    for state in nfa2.accepts:
        nfa1.accepts.update({state + fsa1.states})
    # and adjust the transition function as appropriate
    for letter in nfa1.alphabet:
        # Adjust for fsa2
        # First we deal with 0 as the source
        for target in nfa2.transitions[letter][0]:
            nfa1.transitions[letter][0].update([target + fsa1.states])
        # Then we deal with any other source
        for initial in range(0, nfa2.states):
            for target in nfa2.transitions[letter][initial]:
                nfa1.transitions[letter][initial + fsa1.states].update([target + fsa1.states])
        # And adjust for fsa1
        # Source was 0
        target = fsa1.transitions[letter][0]
        if target != 0:
            nfa1.transitions[letter][nfa1.states - 1].update([fsa1.transitions[letter][0]])
        else:
            nfa1.transitions[letter][nfa1.states - 1].update([nfa1.states - 1])
        # Target was 0
        for source in range(0, fsa1.states):
            if 0 in nfa1.transitions[letter][source]:
                nfa1.transitions[letter][source].symmetric_difference_update({0, nfa1.states - 1})
    # And finally return the appropriate fsa
    out = determinize(nfa1)
    return out

def intersection(fsa1, fsa2):
    if fsa1.states == 1:
        if len(fsa1.accepts) == 1:
            return fsa2
        if len(fsa1.accepts) == 0:
            return fsa1
    if fsa2.states == 1:
        if len(fsa2.accepts) == 1:
            return fsa1
        if len(fsa2.accepts) == 0:
            return fsa2
    # Tested and working.
    # There can be an alphabet error if fsa1 and fsa2 have different alphabets.
    if fsa1.alphabet != fsa2.alphabet:
        raise AlphabetError(fsa1.alphabet, fsa2.alphabet, "In intersection, " + str(fsa1) + " and " + str(fsa2) + " have different alphabets.")
    # This is actually almost like a product, except we then prune all of the non-diagonal letters and relabel them.
    # Eh, I'd rather not have to go through products to do this.
    # States are state1 * fsa2.states + state2
    states = fsa1.states * fsa2.states
    accepts = set()
    alphabet = fsa1.alphabet
    transitions = {}
    # Deal with accept states
    for i in fsa1.accepts:
        for j in fsa2.accepts:
            accepts.update({i * fsa2.states + j})
    # Deal with transition function
    for letter in alphabet:
        transitions[letter] = [0] * states
        for i in range(0, fsa1.states):
            for j in range(0, fsa2.states):
                transitions[letter][i * fsa2.states + j] = fsa1.transitions[letter][i] * fsa2.states + fsa2.transitions[letter][j]
    out = BFS(FSA(states, accepts, alphabet, transitions))
    return out

def quotient(fsa1, fsa2):
    # Tested and working.
    # This spits out all of the words u for which there is some v such that uv is accepted by fsa1 and v is accepted by fsa2.
    # There can be an alphabet error if fsa1 and fsa2 have different alphabets.
    if fsa1.alphabet != fsa2.alphabet:
        raise AlphabetError(fsa1.alphabet, fsa2.alphabet, "In quotient, " + str(fsa1) + " and " + str(fsa2) + " have different alphabets.")
    # Turns out this is easy enough if! you have intersections ready.
    # All you have to do is take fsa1 starting at each state,
    # then intersect with fsa2
    # and if you have a non-empty intersection, that state is an accept state in the quotient fsa
    outStates = fsa1.states
    outAccepts = set()
    outAlphabet = fsa1.alphabet
    outTransitions = fsa1.transitions
    for state in range(0, fsa1.states):
        temp1 = copy.deepcopy(fsa1)
        temp1.changeInit(state)
        temp1 = intersection(temp1, fsa2)
        temp1 = BFS(temp1)
        if len(temp1.accepts) > 0:
            outAccepts.update({state})
    return FSA(outStates, outAccepts, outAlphabet, outTransitions)

def strictQuotient(fsa1, fsa2):
    # This spits out all of the words u such that for all v accepted by fsa2, uv is accepted by fsa1.
    # Note the difference between this and quotient: this requires all words from fsa2 to be acceptable, while quotient requires only one.
    if fsa1.alphabet != fsa2.alphabet:
        raise AlphabetError(fsa1.alphabet, fsa2.alphabet, "In strictQuotient, " + str(fsa1) + " and " + str(fsa2) + " have different alphabets.")
    outStates = fsa1.states
    outAccepts = set()
    outAlphabet = fsa1.alphabet
    outTransitions = fsa1.transitions
    # Again, easy enough if you have intersections.
    # Take fsa1 starting at each state,
    # then intersect with fsa2.
    # If the result is all words accepted by fsa2, that state is an accept state in the strict quotient fsa.
    # (i.e., if the result union complement(fsa2) is the one-state accept.)
    for state in range(0, fsa1.states):
        temp1 = copy.deepcopy(fsa1)
        temp1.changeInit(state)
        temp1 = intersection(temp1, fsa2)
        temp1 = union(temp1, complement(fsa2))
        if temp1.states == 1:
            if temp1.accepts == [0]:
                outAccepts.update({state})
    return FSA(outStates, outAccepts, outAlphabet, outTransitions)

def concatenation(fsa1, fsa2):
    if fsa2.states == 1:
        if len(fsa2.accepts) == 0:
            return fsa2
    # There can be an alphabet error if fsa1 and fsa2 have different alphabets.
    if fsa1.alphabet != fsa2.alphabet:
        raise AlphabetError(fsa1.alphabet, fsa2.alphabet, "In concatenation, " + str(fsa1) + " and " + str(fsa2) + " have different alphabets.")
    # Essentially, we need to copy over the transitions from fsa2's initial state to each of fsa1's accept states
    nfa1 = nondeterminize(fsa1)
    # Update number of states
    for i in range(fsa2.states):
        nfa1.addState()
    # Add the oddball transitions
    for state in nfa1.accepts:
        for let in fsa1.alphabet:
            nfa1.transitions[let][state].update({fsa2.transitions[let][0] + fsa1.states})
    # Update accept states
    for state in fsa2.accepts:
        nfa1.accepts.update({state + fsa1.states})
    if 0 not in fsa2.accepts:
        for state in fsa1.accepts:
            nfa1.accepts.difference_update({state})
    # Add the typical transitions
    for state in range(fsa2.states):
        for let in fsa1.alphabet:
            nfa1.transitions[let][state + fsa1.states].update([fsa2.transitions[let][state] + fsa1.states])
    out = BFS(determinize(nfa1))
    return out

def diagonal(alph):
    # Tested and working
    states = 2
    accepts = {0}
    alphabet = set()
    for let1 in alph:
        for let2 in alph:
            alphabet.update({(let1, let2)})
        alphabet.update({(let1, None)})
        alphabet.update({(None, let1)})
    transitions = {}
    for let in alphabet:
        transitions[let] = [1, 1]
    for let in alph:
        transitions[(let, let)][0] = 0
    return FSA(states, accepts, alphabet, transitions)
    
def projection(fsa, indices):
    # TODO: validity testing
    def isSensible(tup):
        if type(tup) != tuple:
            if tup == None:
                return False
            return True
        for entry in tup:
            if entry != None:
                return True
        return False
    
    out = nondeterminize(fsa)
    alphabet = set()
    transitions = {}
    for let in out.alphabet:
        if len(indices) > 1:
            newLet = tuple(let[i] for i in indices)
        else:
            newLet = let[indices[0]]
        if isSensible(newLet):
            if not newLet in alphabet:
                alphabet.update({newLet})
                transitions[newLet] = []
                for i in range(0, out.states):
                    transitions[newLet].append(set())
            for state in range(0, out.states):
                transitions[newLet][state].update(out.transitions[let][state])
    transitions[None] = {}
    for state in range(0, out.states):
        transitions[None][state] = set()
    out.alphabet = alphabet
    out.transitions = transitions
    return BFS(determinize(out))


def randomFSA(minStates, maxStates, acceptRate, alph):
    states = random.randint(minStates, maxStates)
    accepts = set()
    for i in range(0, states):
        if random.random() < acceptRate:
            accepts.update({i})
    transitions = {}
    for letter in alph:
        transitions[letter] = [0] * states
        for i in range(0, states):
            transitions[letter][i] = random.randint(0, states - 1)
    return FSA(states, accepts, alph, transitions)

def singleSubstitution(fsa1, letter, fsa2):
    # This is still untested!!!! TODO: Test this!!!
    # Here, we're replacing each instance of letter by a copy of fsa2
    # Easiest to do in nfa land, I think
    # I'm doing this as a singleSubstitution; you can do a full substitution as a sufficiently complex chain of singleSubstitutions
    nfa1 = nondeterminize(fsa1)
    # Add all of the letters you need
    for let in fsa2.alphabet:
        if let not in fsa1.alphabet:
            nfa1.addLetter(let)
    # For each edge labeled by letter, we need to add a copy of fsa2, where the source vertex acts like 0 in fsa2 and each accept vertex in fsa2 acts like the target vertex
    for source in range(fsa1.states):
        target = fsa1.transitions[letter][source]
        # Add all the new states
        for state in range(fsa2.states):
            nfa1.addState()
        # Add the fsa2 edges
        for let in fsa2.alphabet:
            for s2 in range(fsa2.states):
                nfa1.transitions[let][nfa1.states - s2].update({nfa1.states - fsa2.transitions[let][s2]})
        # Add the new source edges
        for let in fsa2.alphabet:
            nfa1.transitions[let][source].update({nfa1.states - fsa2.transitions[let][0]})
        # Add the edges out of fsa2 accepts
        for s2 in fsa2.accepts:
            for let in fsa1.alphabet:
                nfa1.transitions[let][nfa1.states - s2].update({fsa1.transitions[let][target]})
    return BFS(determinize(nfa1))

def inverseHomomorphism(fsa, hom):
    # This is still untested!!!! TODO: Test this!!!
    # hom should be a dict with pairings x: h(x)
    # This is actually easiest to do in deterministic land, I think
    alph = set(hom.keys())
    states = fsa.states
    accepts = fsa.accepts
    # The only tricky bit is the transition function; both the states and accepts are pulled straight from fsa.
    # What we need to do is, for each letter a, and each state s, figure out where h(a) goes from s
    # And that's gonna be the new transition function
    transitions = {}
    for let in alph:
        transitions[let] = [0] * states
        for source in range(states):
            target = source
            for let2 in hom[let]:
                target = fsa.transitions[let2][target]
            transitions[let][source] = target
    return BFS(FSA(states, accepts, alph, transitions))

class RegularGrammar:
    def __init__(self, variables, terminals, rules):
        # We assume that the start variable is index 0
        self.variables = variables
        self.terminals = terminals
        self.rules = rules

def NFAFromGrammar(grammar):
    states = len(grammar.variables)
    accepts = set()
    transitions = {}
    for let in grammar.terminals:
        transitions[let] = {}
    transitions[None] = {}
    for let in transitions.keys():
        for state in range(states):
            transitions[let][state] = set()
    for rule in grammar.rules:
        currentState = grammar.variables.index(rule[0])
        if len(rule[1]) == 0:
            # We terminate with a move to an empty string
            accepts.update([grammar.variables.index(rule[0])])
        elif len(rule[1]) > 2 and rule[1][-1] in grammar.variables:
            # We do not terminate but have multiple letters to deal with
            # So we add a bunch of new states and transition appropriately, with our final terminal leading to the variable on the right
            currentState = grammar.variables.index(rule[0])
            for i in range(len(rule[1]) - 2):
                states += 1
                transitions[rule[1][i]][currentState].update({states - 1})
                for let in transitions.keys():
                    transitions[let][states - 1] = set()
                currentState = states - 1
            transitions[rule[1][-2]][currentState].update({grammar.variables.index(rule[1][-1])})
        elif rule[1][-1] in grammar.terminals:
            # We terminate with some number of letters
            # This is much the same as above, actually, just without looping back to a variable's state
            currentState = grammar.variables.index(rule[0])
            for i in range(len(rule[1])):
                states += 1
                transitions[rule[1][i]][currentState].update({states - 1})
                for let in transitions.keys():
                    transitions[let][states - 1] = set()
                currentState = states - 1
            accepts.update([states - 1])
        elif len(rule[1]) == 2:
            # We do not terminate with exactly one letter
            # This requires a transition from left variable to right variable via the terminal
            transitions[rule[1][0]][grammar.variables.index(rule[0])].update({grammar.variables.index(rule[1][-1])})
        elif len(rule[1]) == 1:
            # We do not terminate with no letters
            # This requires an epsilon transition from the left side to the right side.
            transitions[None][grammar.variables.index(rule[0])].update({grammar.variables.index(rule[1][-1])})
    return NFA(states, accepts, grammar.terminals, transitions)

def reverse(nfa):
    states = nfa.states + 1
    transitions = {}
    for let in nfa.alphabet:
        transitions[let] = {}
    transitions[None] = {}
    for let in transitions.keys():
        for state in range(states):
            transitions[let][state] = set()
        for state in range(nfa.states):
            for state2 in nfa.transitions[let][state]:
                transitions[let][state2 + 1].update({state + 1})
    for state in nfa.accepts:
        transitions[None][0].update({state + 1})
    return NFA(states, [1], nfa.alphabet, transitions)


