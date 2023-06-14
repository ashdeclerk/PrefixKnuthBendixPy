#####
# Ordering Automata
# Developed by Ash DeClerk (declerk.gary@huskers.unl.edu) for use in their Prefix-Knuth-Bendix program
# Last updated 9/18/2022
#####

import FSA # Ash DeClerk's FSA module

def Short(alphabet):
    # This function creates an FSA accepting pairs of words (u, v) such that v is shorter than u.
    alph = set()
    for let in alphabet:
        for let2 in alphabet:
            alph.update({(let, let2)})
        alph.update({(None, let)})
        alph.update({(let, None)})
    states = 3
    # State 0 is the "so far neither u nor v have terminated" state, and is not accepting
    # State 1 is the "v has terminated but u has not terminated" state, and is accepting
    # State 2 is the Fail state, and is not accepting
    transitions = {}
    for let in alph:
        transitions[let] = [2] * states
    for let in alphabet:
        for let2 in alphabet:
            transitions[(let, let2)][0] = 0
        transitions[(let, None)][0] = 1
        transitions[(let, None)][1] = 1
    accepts = {1}
    return FSA.FSA(states, accepts, alph, transitions)

def ShortTie(alphabet):
    # This function creates an FSA accepting pairs of words (u, v) such that u and v have the same length.
    alph = set()
    for let in alphabet:
        for let2 in alphabet:
            alph.update({(let, let2)})
        alph.update({(None, let)})
        alph.update({(let, None)})
    states = 2
    # State 0 is the "so far neither u nor v have terminated" state, and is accepting
    # State 2 is the Fail state, and is not accepting
    transitions = {}
    for let in alph:
        transitions[let] = [1] * states
    for let in alphabet:
        for let2 in alphabet:
            transitions[(let, let2)][0] = 0
    accepts = {0}
    return FSA.FSA(states, accepts, alph, transitions)

def Slex(alphabet):
    # TODO: Test
    # This function creates an FSA accepting pairs of words (u, v) such that v is shorter than u,
    # or u and v have the same length and v is lexicographically smaller than u
    # Note that alphabet needs to be ordered.
    alph = set()
    for let in alphabet:
        for let2 in alphabet:
            alph.update({(let, let2)})
        alph.update({(None, let)})
        alph.update({(let, None)})
    states = 5
    # State 0 is the "so far u and v are identical state", and is not accepting
    # State 1 is the "u is lexicographically smaller than v but neither has ended" state, and is not accepting
    # State 2 is the "v is lexicographically smaller than u but neither has ended" state, and is accepting
    # State 3 is the "v has ended but u has not" state, and is accepting
    # State 4 is the "we have failed" state, and is not accepting
    transitions = {}
    for let in alph:
        transitions[let] = [4] * states
    # I'm going to deal with these on a state-by-state basis
    # State 0: on (a, a), we stay at 0
    for let in alphabet:
        transitions[(let, let)][0] = 0
    # on (a, b) for b after a, we move to 1
    # and on (b, a) for b after a, we move to 2
    for i in range(1, len(alphabet)):
        for j in range(0, i):
            transitions[(alphabet[i], alphabet[j])][0] = 2
            transitions[(alphabet[j], alphabet[i])][0] = 1
    # on (a, None) we move to 3
    # and on (None, a) we move to 4, which is default
    for let in alphabet:
        transitions[(let, None)][0] = 3
    # State 1: on (a, b) we stay at 1
    for let in alphabet:
        for let2 in alphabet:
            transitions[(let, let2)][1] = 1
    # on (a, None) we move to 3
    # and on (None, a) we move to 4, which is default
    for let in alphabet:
        transitions[(let, None)][1] = 3
    # State 2: on (a, b) we stay at 2
    for let in alphabet:
        for let2 in alphabet:
            transitions[(let, let2)][2] = 2
    # on (a, None) we move to 3
    # and on (None, a) we move to 4, which is default
    for let in alphabet:
        transitions[(let, None)][2] = 3
    # State 3: on (a, b) we move to 4 since v has a gap
    # (but that's the default)
    # likewise for (None, a)
    # but for (a, None) we stay at 3
    for let in alphabet:
        transitions[(let, None)][3] = 3
    accepts = {2, 3}
    return FSA.FSA(states, accepts, alph, transitions)


def RegSplitSlex(fsa, perms):
    # This function creates an FSA accepting pairs of words (u, v) such that v is shorter than u,
    # or u and v have the same length and v is lexicographically smaller than u
    # with the specific lex ordering depending on the state that the longest common prefix of u and v lands at in fsa.
    # Note that perms should be a dictionary, with keys corresponding to states of fsa and entries being fsa.alphabet sorted appropriately for that state
    # This is gonna be fuuuun.
    # First, we figure out the appropriate number of states. One per original state, plus four common states for slex things.
    # fsa.states is the "v is lex smaller than u but neither has ended" state
    # fsa.states + 1 is "u is lex smaller than v but neither has ended"
    # fsa.states + 2 is "v is shorter than u"
    # and fsa.states + 3 is "fail"
    states = fsa.states + 4
    accepts = {states - 4, states - 2}
    # Set up the alphabet appropriately
    alph = set()
    for let in fsa.alphabet:
        for let2 in fsa.alphabet:
            alph.update({(let, let2)})
        alph.update({(None, let)})
        alph.update({(let, None)})
    # And set up the nightmare of a transition function.
    transitions = {}
    for let in alph:
        transitions[let] = [states - 1] * states
    for let in fsa.alphabet:
        # Deal with slex state transitions
        transitions[(let, None)][states - 4] = states - 2
        transitions[(let, None)][states - 3] = states - 2
        transitions[(let, None)][states - 2] = states - 2
        for let2 in fsa.alphabet:
            transitions[(let, let2)][states - 4] = states - 4
            transitions[(let, let2)][states - 3] = states - 3
    for oldState in range(0, fsa.states):
        for let in fsa.alphabet:
            # Deal with original fsa transitions
            transitions[(let, let)][oldState] = fsa.transitions[let][oldState]
            # And length-based transitions for slex
            transitions[(let, None)][oldState] = states - 2
        # And finally, deal with the perm-based transitions for slex
        for i in range(1, len(fsa.alphabet)):
            for j in range(0, i): # j is strictly smaller than i
                transitions[(perms[oldState][i], perms[oldState][j])][oldState] = states - 4
                transitions[(perms[oldState][j], perms[oldState][i])][oldState] = states - 3
    for key, item in transitions.items():
        transitions[key] = tuple(item)
    return FSA.FSA(states, accepts, alph, transitions)

def RegSplitSlexFromUnion(defaultOrd, automata):
    # This function creates an FSA for regular-split shortlex, but built from slightly different information than the one above.
    # In particular, we have a "default" ordering, and a dictionary of orderings and an FSA accepting the prefixes where that ordering is the one we prefer.
    # For some groups, it might make more sense to use this method to make the order automaton.
    # NB: It is assumed that the FSAs have no overlap. Again, IT IS ASSUMED THAT THE FSAS ARE PAIRWISE DISJOINT.
    # If the FSAs aren't pairwise disjoint, you'll get something that's not an order. That's on you!
    alph = set()
    for let in defaultOrd:
        for let2 in defaultOrd:
            alph.update({(let, let2)})
        alph.update({(None, let)})
        alph.update({(let, None)})
    out = FSA.emptyFSA(alph)
    unclaimedPrefixes = FSA.allFSA(alph)
    # What we need to do is union with each fsa accepting all (paw, pbw) such that a < b after L, p is in L, and w is any word
    # So, we're going to grab each (order, fsa) pair in automata, build the fsa for that pair, and union it to out.
    diag = FSA.diagonal(set(defaultOrd))
    for order, fsa in automata.items():
        newFsa = FSA.product(fsa, fsa)
        newFsa = FSA.intersection(newFsa, diag)
        unclaimedPrefixes = FSA.intersection(unclaimedPrefixes, FSA.complement(newFsa))
        suffix = FSA.emptyFSA(alph)
        for i, let1 in enumerate(order):
            for j, let2 in enumerate(order[i + 1:], i + 1):
                suffix = FSA.union(suffix, FSA.singFSA(set(defaultOrd), (let2, let1)))
        newFsa = FSA.concatenate(newFsa, suffix)
        out = FSA.union(out, newFsa)
    # For unclaimed prefixes, we use defaultOrd
    suffix = FSA.emptyFSA(alph)
    for i, let1 in enumerate(defaultOrd):
        for j, let2 in enumerate(defaultOrd[i + 1:], i + 1):
            suffix = FSA.union(suffix, FSA.singFSA((let2, let1)))
    newFsa = FSA.concatenate(unclaimedPrefixes, suffix)
    out = FSA.union(out, newFsa)
    out = FSA.concatenate(out, FSA.allFSA(alph))
    return out

def Srevlex(alphabet):
    # TODO: Test
    # Short reverse lexicographic order
    # This is very similar to Slex, but slightly simpler
    alph = set()
    for let in alphabet:
        for let2 in alphabet:
            alph.update({(let, let2)})
        alph.update({(None, let)})
        alph.update({(let, None)})
    states = 5
    # State 0 is the "so far u and v are identical" state
    # State 1 is the "the most recent different letter was smaller for u, and neither word has ended" state
    # State 2 is the "the most recent different letter was smaller for v, and neither word has ended" state
    # State 3 is the "v has ended, but u has not" state
    # State 4 is the "we have failed" state
    transitions = {}
    for let in alph:
        transitions[let] = [4] * states
    # Deal with (a, a) and ($, a)
    for let in alphabet:
        transitions[(let, let)][0] = 0
        transitions[(let, let)][1] = 1
        transitions[(let, let)][2] = 2
        transitions[(let, None)][0] = 3
        transitions[(let, None)][1] = 3
        transitions[(let, None)][2] = 3
        transitions[(let, None)][3] = 3
    # Deal with (a, b)
    for i in range(1, len(alphabet)):
        for j in range(0, i):
            transitions[(alphabet[i], alphabet[j])][0] = 2
            transitions[(alphabet[j], alphabet[i])][0] = 1
            transitions[(alphabet[i], alphabet[j])][1] = 2
            transitions[(alphabet[j], alphabet[i])][1] = 1
            transitions[(alphabet[i], alphabet[j])][2] = 2
            transitions[(alphabet[j], alphabet[i])][2] = 1
    accepts = {2, 3}
    return FSA.FSA(states, accepts, alph, transitions)

def AsynchOrderedSquareAutomaton(fsa, ordering):
    # TODO: Test
    # This function takes an FSA and a (partial) ordering on the states of that FSA,
    # and returns an (asynchronous) FSA accepting pairs (u, v) where u ends at a state p and v ends at a state q with p > q.
    # The ordering should be given as a fsa.states * fsa.states - long list,
    # with entry fsa.states * i + j having a 1 for "i > j" and a 0 else.
    # Alphabet is the usual square plus padding
    alph = set()
    for let1 in fsa.alphabet:
        for let2 in fsa.alphabet:
            alph.update({(let1, let2)})
        alph.update({(let1, None)})
        alph.update({(None, let1)})
    # We essentially need to track location in fsa for both u and v.
    # Technically we should probably track padding as well, but I'd prefer to do that as an intersect with a padding problem-detector.
    # So, without tracking padding, we need to have fsa.states ** 2 states
    states = fsa.states ** 2
    accepts = set()
    transitions = {}
    for let in alph:
        transitions[let] = [0] * states
    # And transitions are straightforward enough.
    # We just need to take fsa.states * i + j to fsa.states * a(i) + b(j) on input (a, b)
    for i in range(0, fsa.states):
        for j in range(0, fsa.states):
            # We may as well check ordering here, too
            if ordering[fsa.states * i + j] == 1:
                accepts.update({fsa.states * i + j})
            for let1 in fsa.alphabet:
                for let2 in fsa.alphabet:
                    transitions[(let1, let2)][fsa.states * i + j] = fsa.states * fsa.transitions[let1][i] + fsa.transitions[let2][j]
                transitions[(let1, None)][fsa.states * i + j] = fsa.states * fsa.transitions[let1][i] + j
                transitions[(None, let1)][fsa.states * i + j] = fsa.states * i + fsa.transitions[let1][j]
    return FSA.FSA(states, accepts, alph, transitions)

def PaddingProblemDetector(alphabet):
    # TODO: Test
    # This function takes an alphabet and returns an FSA that accepts exactly the pairs of words over alphabet \cup None with None showing up only at the end of each word.
    # i.e., it accepts well-padded pairs.
    # I'm using this same alphabet everywhere. Perhaps we should spin it into its own function.
    alph = set()
    for let1 in alphabet:
        for let2 in alphabet:
            alph.update({(let1, let2)})
        alph.update({(let1, None)})
        alph.update({(None, let1)})
    # We only need 4 states: "neither word has ended", "the first word has ended", "the second word has ended", and "fail"
    states = 4
    accepts = {0, 1, 2}
    transitions = {}
    for let in alph:
        transitions[let] = [0] * 4
    for let1 in alphabet:
        transitions[(let1, None)][0] = 2
        transitions[(let1, None)][1] = 3
        transitions[(let1, None)][2] = 2
        transitions[(let1, None)][3] = 3
        transitions[(None, let1)][0] = 1
        transitions[(None, let1)][1] = 1
        transitions[(None, let1)][2] = 3
        transitions[(None, let1)][3] = 3
    return FSA.FSA(states, accepts, alph, transitions)

def OrderedSquareAutomaton(fsa, ordering):
    # TODO: Test
    # Synchronous version of AsynchOrderedSquareAutomaton
    # I love it when I can make one-line functions.
    return FSA.intersection(AsynchOrderedSquareAutomaton(fsa, ordering), PaddingProblemDetector(fsa.alphabet))

def LengthProblemDetector(alphabet, length):
    # TODO: Test
    # This function takes an alphabet and length and returns an FSA that accepts exactly the pairs of words over alphabet \cup None with at most length None's at the end of either word.
    # i.e., it prevents one word from being too much longer than the other.
    alph = set()
    for let1 in alphabet:
        for let2 in alphabet:
            alph.update({(let1, let2)})
        alph.update({(let1, None)})
        alph.update({(None, let1)})
    # We need length + 2 states, with all but the last being accepts
    states = length + 2
    accepts = set(range(length + 1))
    transitions = {}
    for let in alph:
        transitions[let] = [0] * states
        transitions[let][states - 1] = states - 1
    for let1 in alphabet:
        for i in range(states - 1):
            transitions[(let1, None)][i] = i + 1
            transitions[(None, let1)][i] = i + 1
    return FSA.intersection(PaddingProblemDetector(alphabet), FSA.FSA(states, accepts, alph, transitions))

# A few useful functions for rpo (and potentially other FSAs that attempt to emulate a stack automaton).
def stackLength(integer, base):
    # The stack state is given by a base-ary number; 0 is the empty stack, 1 through base has all stacks with a single letter, base + 1 through base + base^2 has all stacks of size 2,
    # and in general (base ** k - 1) // (base - 1) through (base ** (k + 1) - 1) // (base - 1) - 1 has all stacks of size k.
    # Looking at the base-ary expansion of i - (base ** k - 1) // (base - 1) spits out the stack, with most recent entries first.
    k = 0
    maxInt = 0
    while True:
        if maxInt >= integer:
            return k
        k += 1
        maxInt += base ** k

def stackLast(integer, base, length):
    # I anticipate stackLength being extra slow. Calc it once and use it again multiple times.
    return (integer - (base ** length - 1) // (base - 1)) % base

def stackPush(integer, base, number, length):
    # length here is the length of the original stack; likewise in stackPop.
    integer -= (base ** length - 1) // (base - 1)
    integer += number * (base ** length)
    integer += (base ** (length + 1) - 1) // (base - 1)
    return integer

def stackPop(integer, base, length):
    integer -= (base ** length - 1) // (base - 1)
    integer -= (integer % base)
    integer //= base
    integer += (base ** (length - 1) - 1) // (base - 1)
    return integer

class layerOrdering:
    # For use in rpo. These are partial orderings where if a < b and b and c are incomparable, then b < c (and similar with >).
    # Basically, we're splitting things into layers.
    def __init__(self, alphabet, layers, assignment):
        # alphabet is all of the symbols
        # layers is the number of layers
        # assignment is a dictionary where keys are symbols and entries are the layer that symbol lives in. Lowest layer is 0, highest is layers - 1.
        self.alphabet = alphabet
        self.layers = layers
        self.assignment = assignment

def leftrpo(ordering, length):
    # Okay, so, leftrpo: given u = au', v = bv', u > v if:
    #   a > b and u > v'; or
    #   u' >= v; or
    #   a = b and u' > v'
    # We want to allow for orderings where multiple letters are in the same level, because that's relevant for BS(1, 2) (and presumably other groups as well),
    # so ordering should be a list of sets, with later sets being larger than earlier sets.
    # The plan is to essentially model a first-in-first-out stack automaton, where the stack stores which level each letter (of the "winning" word) was in.
    # Because of what we're storing in the stack, we need to have (len(ordering) ** (length + 1) - 1) // (len(ordering) - 1) states for each stack automaton state.
    # There are 3 stack automaton states, which are:
    # j = 0, neither ahead (i.e., the stack is empty because so far all letters have been in the same layers on each word)
    # j = 1, left ahead (i.e., the stack is storing letters from left because letters from right are being killed, or the stack is empty because left exactly caught up to right)
    # j = 2, right ahead (i.e., the stack is storing letters from right because letters from left are being killed, or the stack is empty because right exactly caught up to left)
    # This is, as you might expect, a pain in the rear.
    base = ordering.layers
    alphabet = ordering.alphabet
    assignment = ordering.assignment
    alph = set()
    for let1 in alphabet:
        for let2 in alphabet:
            alph.update({(let1, let2)})
        alph.update({(let1, None)})
        alph.update({(None, let1)})
    states = 1 + 2 * (base ** (length + 1) - 1) // (base - 1)
    trueAccepts = set()
    tieAccepts = {0}
    transitions = {}
    for let in alph:
        transitions[let] = [0] * states
    # It's relatively easy to deal with state 0
    for let1 in alphabet:
        for let2 in alphabet:
            if assignment[let1] == assignment[let2]:
                transitions[(let1, let2)][0] = 0
            elif assignment[let1] > assignment[let2]:
                transitions[(let1, let2)][0] = 2 * (1 + assignment[let1]) + 1
            else:
                transitions[(let1, let2)][0] = 2 * (1 + assignment[let2]) + 2
        transitions[(let1, None)][0] = 2 * (1 + assignment[let1]) + 1
        transitions[(None, let1)][0] = 2 * (1 + assignment[let1]) + 2
    for i in range(0, (base ** (length + 1) - 1) // (base - 1)):
        trueAccepts.update({2 * i + 1})
        # And now, the transition function
        # We need to calculate what happens to the stack; that's the *main* problem, though there's some handling of stack automaton state based on the stack changes, too.
        length = stackLength(i, base)
        last = stackLast(i, base, length)
        for let1 in alphabet:
            for let2 in alphabet:
                # Start by dealing with j = 1
                # We first push the layer for let1, then pop (from bottom of stack) everything that's lower than the layer for let2, along with the layer of let2 itself at most once.
                stack = i
                stack = stackPush(i, base, assignment[let1], length)
                curLen = length + 1
                while curLen > 0 and stackLast(stack, base, curLen) < assignment[let2]:
                    stackPop(stack, base, curLen)
                    curLen -= 1
                if curLen == 0:
                    # Right is now ahead and has a letter surviving
                    transitions[(let1, let2)][2 * i + 1] = 2 * (1 + assignment[let2]) + 2
                else:
                    if stackLast(stack, base, curLen) == assignment[let2]:
                        stackPop(stack, base, curLen)
                        curLen -= 1
                    if curLen == 0:
                        # Right is now ahead, but its letter did not survive
                        transitions[(let1, let2)][2 * i + 1] = 2
                    else:
                        # Left is still ahead
                        transitions[(let1, let2)][2 * i + 1] = 2 * stack + 1
                # And now we do the same thing for j = 2
                stack = i
                stack = stackPush(i, base, assignment[let2], length)
                curLen = length + 1
                while curLen > 0 and stackLast(stack, base, curLen) < assignment[let1]:
                    stackPop(stack, base, curLen)
                    curLen -= 1
                if curLen == 0:
                    # Left is now ahead and has a letter surviving
                    transitions[(let1, let2)][2 * i + 2] = 2 * (1 + assignment[let1]) + 1
                else:
                    if stackLast(stack, base, curLen) == assignment[let1]:
                        stackPop(stack, base, curLen)
                        curLen -= 1
                    if curLen == 0:
                        # Left is now ahead, but its letter did not survive
                        transitions[(let1, let2)][2 * i + 2] = 1
                    else:
                        # Right is still ahead
                        transitions[(let1, let2)][2 * i + 2] = 2 * stack + 2
            # And, of course, we have to do basically the same thing with None
            stack = i
            stack = stackPush(i, base, assignment[let1], length)
            transitions[(let1, None)][2 * i + 1] = 2 * stack + 1
            transitions[(None, let1)][2 * i + 2] = 2 * stack + 2
            stack = i
            curLen = length
            while curLen > 0 and stackLast(stack, base, curLen) < assignment[let1]:
                stackPop(stack, base, curLen)
                curLen -= 1
            if curLen == 0:
                transitions[(None, let1)][2 * i + 1] = 2 * (1 + assignment[let1]) + 2
                transitions[(let1, None)][2 * i + 2] = 2 * (1 + assignment[let1]) + 1
            else:
                if stackLast(stack, base, curLen) == assignment[let1]:
                    stackPop(stack, base, curLen)
                    curLen -= 1
                if curLen == 0:
                    transitions[(None, let1)][2 * i + 1] = 2
                    transitions[(let1, None)][2 * i + 2] = 1
                else:
                    transitions[(None, let1)][2 * i + 1] = 2 * stack + 1
                    transitions[(let1, None)][2 * i + 2] = 2 * stack + 2
    return (FSA.BFS(FSA.FSA(states, trueAccepts, alph, transitions)), FSA.BFS(FSA.FSA(states, tieAccepts, alph, transitions)))

def rightrpo(ordering, length):
    # Right rpo is just like left rpo, except reading in reverse. Which means it's much more annoying to work with.
    # Or at least more annoying to think about. We can use the same basic strategy of mimicking a first-in-first-out stack automaton.
    # That said, it's not a priority right now. I'll work on this *later*.
    pass
