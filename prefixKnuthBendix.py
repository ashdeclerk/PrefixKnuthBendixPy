#####
# Prefix-Knuth-Bendix implemented in Python
# Designed and coded by Ash DeClerk (declerk.gary@huskers.unl.edu)
# Version 1.2
# Last updated on 4/20/2023
#####

"""
Goals of version 1.2:
    Main thing here is just adding a function to prune redundant rules.
"""

"""
Goals of version 1.1:
    This version is primarily for efficiency and quality of life updates. My primary goals are:
    - improve speed
        - This was mostly done by adding caching for the most common FSA operations
    - improve memory efficiency
        - todo: the main way to do this is to only have a single copy of any given rule
        - todo: after implementing, test what's going on
    - include verbosity choices
        - I want to have a few levels of verbosity, which are independent
        - 0: prints when the program halts
        - 1: updates at each major step (default setting)
        - 2: print rules at every major step
        - 3: print whenever we update rules or pairs or unresolved
        - 4: print all the extra stuff, like orienting pairs
    - include logging to file rather than just printing as an option
    - improve how things are displayed
        - todo: this is mostly "we need to print autostackable structures in a nice way rather than as dicts"
"""

"""
The goal of pKB is to take a finite presentation for a group and a "sufficiently nice" ordering,
(though I think a regular presentation might also be workable),
and turn that into a regular convergent prefix-rewriting system
(though with a finite presentation this will necessarily also be bounded, hence an autostackable structure).
Pseudocode for the grand scheme of things:
    Input: A group and an ordering.
        We'll need to define classes for each, I think.
    First step:
        Generate a list of rules (empty at start)
        Generate three lists of pairs (IntPairs, ExtPairs, and PrePairs)
        Populate the above lists
        Also make an empty list Unresolved
    Repeat the following two steps until a termination condition:
    Critical Pair Checking step:
        Check IntPairs for an interior critical pairs, i.e. l_2 is a subword of l_1
        If IntPairs started empty, check ExtPairs for external critical pairs, i.e. l_1 has a suffix that is a proper prefix of l_2
        If both IntPairs and ExtPairs started empty, check PrePairs for prefix critical pairs, i.e. ul_1v \in L_2 but ur_1v \not\in L_2
        Whichever list you end up checking, move all critical pairs to Unresolved
    Equality Resolution step:
        For each equality in Unresolved, do the following:
            if L = \empty, toss
            else:
                find descendents of both sides of the equality
                (these will be pairs (J, w) of a language and a word that is reduced after that language)
                for each pair (J_1, w_1), (J_2, w_2), find three sets:
                    K_1, which is all words in J_1 \cap J_2 after which w_1 is smaller than w_2
                    K_2, which is all words in J_1 \cap J_2 after which w_2 is smaller than w_1
                    K_3, which is all words in J_1 \cap J_2 after which w_1 and w_2 are incomparable
                add the rules K_1: w_2 \to w_1 and K_2: w_1 \to w_2
                return K_3: w_1 = w_2 to newUnresolved
        At this point, Unresolved should be empty and newUnresolved should only have equalities that are incomparable, so migrate newUnresolved to Unresolved
    Termination condition is that all three lists of pairs are empty after a resolution step
    If Unresolved is empty, we're done!
    Else, we have to do more fussy stuff:
        Prefix resolution step:
            (This is really an "oh shit, I'm running really low on options" step)
            For each unresolved equality:
                Prune the prefix language to irreducibles
                If the prefix language is empty, toss the equality, because it's all reducible words
                Next, do additional reductions of the form
                    wu = al_ib -> ar_ib, for a \in L_i, w \in L, b any word
                    Except, y'know, with reglang-y stuff
            If Unresolved is empty now, then you're done
            If you did any reductions of the second type, go back to the equality resolution step
            Else, scream at the user about updating their ordering
    Anyway, spit out all of the rules and any unresolved critical pairs. Possibly as a new group object with that information attached.
"""

import FSA # Ash DeClerk's (that's me!) FSA module, which we'll be using for all finite state automata.
import copy
import time


# Several caches to improve efficiency
# It turns out that calculating the same intersection a hundred times is slow.
intersectionCache = {}
def intersection(fsa1, fsa2):
    frozenfsa1 = FSA.freeze(fsa1)
    frozenfsa2 = FSA.freeze(fsa2)
    if frozenfsa1 in intersectionCache:
        if frozenfsa2 in intersectionCache[frozenfsa1]:
            return intersectionCache[frozenfsa1][frozenfsa2]
    if frozenfsa2 in intersectionCache:
        if frozenfsa1 in intersectionCache[frozenfsa2]:
            return intersectionCache[frozenfsa2][frozenfsa1]
    if frozenfsa1 not in intersectionCache:
        intersectionCache[frozenfsa1] = {}
    fsa3 = FSA.intersection(fsa1, fsa2)
    intersectionCache[frozenfsa1][frozenfsa2] = fsa3
    return fsa3


quotientCache = {}
def quotient(fsa1, fsa2):
    frozenfsa1 = FSA.freeze(fsa1)
    frozenfsa2 = FSA.freeze(fsa2)
    if frozenfsa1 in quotientCache:
        if frozenfsa2 in quotientCache[frozenfsa1]:
            return quotientCache[frozenfsa1][frozenfsa2]
    if frozenfsa1 not in quotientCache:
        quotientCache[frozenfsa1] = {}
    fsa3 = FSA.quotient(fsa1, fsa2)
    quotientCache[frozenfsa1][frozenfsa2] = fsa3
    return fsa3

BFSCache = {}
def BFS(fsa1):
    frozenfsa1 = FSA.freeze(fsa1)
    if frozenfsa1 in BFSCache:
        return BFSCache[frozenfsa1]
    fsa2 = FSA.BFS(fsa1)
    BFSCache[frozenfsa1] = fsa2
    return fsa2

diagonalCache = {}
def diagonal(alphabet):
    frozenalph = frozenset(alphabet)
    if frozenalph in diagonalCache:
        return diagonalCache[frozenalph]
    fsa1 = FSA.diagonal(alphabet)
    diagonalCache[frozenalph] = fsa1
    return fsa1

complementCache = {}
def complement(fsa1):
    frozenfsa = FSA.freeze(fsa1)
    if frozenfsa in complementCache:
        return complementCache[frozenfsa]
    fsa2 = FSA.complement(fsa1)
    complementCache[frozenfsa] = fsa2
    return fsa2

concatenationCache = {}
def concatenation(fsa1, fsa2):
    frozenfsa1 = FSA.freeze(fsa1)
    frozenfsa2 = FSA.freeze(fsa2)
    if frozenfsa1 in concatenationCache:
        if frozenfsa2 in concatenationCache[frozenfsa1]:
            return concatenationCache[frozenfsa1][frozenfsa2]
    if frozenfsa1 not in concatenationCache:
        concatenationCache[frozenfsa1] = {}
    fsa3 = FSA.concatenation(fsa1, fsa2)
    concatenationCache[frozenfsa1][frozenfsa2] = fsa3
    return fsa3

singFSACache = {}
def singFSA(alphabet, word):
    alph = frozenset(alphabet)
    frword = tuple(word)
    if alph in singFSACache:
        if frword in singFSACache[alph]:
            return singFSACache[alph][frword]
    if alph not in singFSACache:
        singFSACache[alph] = {}
    fsa = FSA.singFSA(alphabet, word)
    singFSACache[alph][frword] = fsa
    return fsa

productCache = {}
def product(fsa1, fsa2):
    frozenfsa1 = FSA.freeze(fsa1)
    frozenfsa2 = FSA.freeze(fsa2)
    if frozenfsa1 in productCache:
        if frozenfsa2 in productCache[frozenfsa1]:
            return productCache[frozenfsa1][frozenfsa2]
    if frozenfsa1 not in productCache:
        productCache[frozenfsa1] = {}
    fsa3 = FSA.product(fsa1, fsa2)
    productCache[frozenfsa1][frozenfsa2] = fsa3
    return fsa3

projectionCache = {}
def projection(fsa1, indices):
    frozenfsa1 = FSA.freeze(fsa1)
    frozenindices = tuple(indices)
    if frozenfsa1 in projectionCache:
        if frozenindices in projectionCache[frozenfsa1]:
            return projectionCache[frozenfsa1][frozenindices]
    if frozenfsa1 not in projectionCache:
        projectionCache[frozenfsa1] = {}
    fsa2 = FSA.projection(fsa1, indices)
    projectionCache[frozenfsa1][frozenindices] = fsa2
    return fsa2

def clearCaches():
    intersectionCache = {}
    quotientCache = {}
    BFSCache = {}
    diagonalCache = {}
    complementCache = {}
    concatenationCache = {}
    singFSACache = {}
    productCache = {}
    projectionCache = {}
    return None



class AutostackableStructure:
    # This is largely a data storage class.
    # Todo for future: add functionality. For example, reducing a word to its normal form.

    def __init__(self, isConvergent, Rules, IntPairs, ExtPairs, PrePairs, Unresolved):
        self.isConvergent = isConvergent
        self.Rules = Rules
        if isConvergent:
            pass
        else:
            self.IntPairs = IntPairs
            self.ExtPairs = ExtPairs
            self.PrePairs = PrePairs
            self.Unresolved = Unresolved

    def __repr__(self):
        out = 'Is convergent: ' + str(self.isConvergent) + '\n'
        out += '---\n'
        out += 'Rules are: \n\n'
        for rule in self.Rules:
            out += str(rule) + '\n\n'
        if self.isConvergent:
            pass
        else:
            out += '---\n'
            out += 'Interior Pairs are: \n'
            for pair in self.IntPairs:
                out += str(pair) + '\n'
            out += '---\n'
            out += 'Exterior Pairs are: \n'
            for pair in self.ExtPairs:
                out += str(pair) + '\n'
            out += '---\n'
            out += 'Prefix Pairs are: \n'
            for pair in self.PrePairs:
                out += str(pair) + '\n'
            out += '---\n'
            out += 'Unresolved Equations are: \n'
            for pair in self.Unresolved:
                out += str(pair) + '\n'
        return out
        


class Group:

    # A Group object contains all information currently known about a group.
    # The only required pieces of info are generators and relators
    # (presented however you like, though I'll be assuming that they're given as finite lists),
    # but other information can be provided as desired.
    # In particular, our current program will also want to store P-RS information with the group.
    # The lovely thing about python's objects is that they'll just store whatever you want them to store.

    def __init__(self, generators, relators):
        self.generators = generators
        self.relators = relators


def IntPairCheck(IntPairs, ExtPairs, PrePairs, Unresolved, alphabet, Rules):
    # Check all pairs of rules from IntPairs for interior critical pairs
    # That is, any instance where the second word is a subword of the first word
    # In those cases (with the right prefix language intersections), we have ambiguous rewriting of left1 to either right1 or p*right2*s for some p and s
    while len(IntPairs) > 0:
        pair = IntPairs.pop()
        pair[0] = Rules[pair[0]]
        pair[1] = Rules[pair[1]]
        vprint3('Checking for interior pairs between', pair[0], 'and', pair[1])
        lprint3('Checking for interior pairs between', pair[0], 'and', pair[1])
        # We're looking for l1 to be a subword of l2
        for index in range(0, len(pair[1][1]) - len(pair[0][1]) + 1):
            if pair[0][1] == pair[1][1][index: index + len(pair[0][1])]:
                word1 = copy.copy(pair[1][2])
                word2 = copy.copy(pair[1][1])
                word2[index:index + len(pair[0][1])] = pair[0][2]
                # Hoo boy, we get to deal with the prefix language.
                # This is ((L2 . pair[1][1][0:index]) \cap L1) / pair[1][1][0:index]
                # See the paper for an explanation of why.
                prefixes = copy.deepcopy(pair[1][0])
                prefixes = concatenation(prefixes, singFSA(alphabet, pair[1][1][0:index]))
                prefixes = intersection(prefixes, pair[0][0])
                prefixes = quotient(prefixes, singFSA(alphabet, pair[1][1][0:index]))
                prefixes = BFS(prefixes)
                while len(word1) > 0 and len(word2) > 0 and word1[-1] == word2[-1]:
                    del word1[-1]
                    del word2[-1]
                p = []
                while len(word1) > 0 and len(word2) > 0 and word1[0] == word2[0]:
                    p.append(word1.pop(0))
                    del word2[0]
                rawPrefixes = copy.deepcopy(prefixes)
                if len(p) > 0:
                    prefixes = concatenation(prefixes, singFSA(prefixes.alphabet, p))
                vprint3('Adding equation', [prefixes, word1, word2])
                lprint3('Adding equation', [prefixes, word1, word2])
                Unresolved.append([prefixes, word1, word2])
                # We also need to find and prune the old rule from Rules and update all of the Pairs lists. For efficiency purposes, mostly.
                deletedRuleIndices = []
                for jndex in range(0, len(Rules)):
                    if Rules[jndex][1] == pair[1][1]:
                        if Rules[jndex][2] == pair[1][2]:
                            Rules[jndex][0] = BFS(intersection(Rules[jndex][0], complement(rawPrefixes)))
                            # At one point the second jndex here was an index, which was obviously bad. Reasons not to use similar variable names.
                            if len(Rules[jndex][0].accepts) == 0:
                                deletedRuleIndices.append(jndex)
                while len(deletedRuleIndices) > 0:
                    jndex = deletedRuleIndices.pop(-1)
                    vprint3('Removing redundant rule', Rules[jndex])
                    lprint3('Removing redundant rule', Rules[jndex])
                    del Rules[jndex]
                    # The dead rule has been removed, but now we need to go through IntPairs, ExtPairs, and PrePairs
                    for k in list(range(len(IntPairs) - 1, -1, -1)):
                        if IntPairs[k][0] == jndex or IntPairs[k][1] == jndex:
                            del IntPairs[k]
                        else:
                            if IntPairs[k][0] > jndex:
                                IntPairs[k][0] -= 1
                            if IntPairs[k][1] > jndex:
                                IntPairs[k][1] -= 1
                    for k in list(range(len(ExtPairs) - 1, -1, -1)):
                        if ExtPairs[k][0] == jndex or ExtPairs[k][1] == jndex:
                            del ExtPairs[k]
                        else:
                            if ExtPairs[k][0] > jndex:
                                ExtPairs[k][0] -= 1
                            if ExtPairs[k][1] > jndex:
                                ExtPairs[k][1] -= 1
                    for k in list(range(len(PrePairs) - 1, -1, -1)):
                        if PrePairs[k][0] == jndex or PrePairs[k][1] == jndex:
                            del PrePairs[k]
                        else:
                            if PrePairs[k][0] > jndex:
                                PrePairs[k][0] -= 1
                            if PrePairs[k][1] > jndex:
                                PrePairs[k][1] -= 1
                
                

def ExtPairCheck(ExtPairs, Unresolved, alphabet, Rules):
    # This function searches for exterior critical pairs
    # That is, places where a suffix of one LHS matches the prefix of another LHS
    # In this case, we have ambiguous rewriting to either right1 * s or p * right2
    while len(ExtPairs) > 0:
        pair = ExtPairs.pop()
        pair[0] = Rules[pair[0]]
        pair[1] = Rules[pair[1]]
        vprint3('Checking for external critical pairs between', pair[0], 'and', pair[1])
        lprint3('Checking for external critical pairs between', pair[0], 'and', pair[1])
        # We're looking for a proper suffix of l1 to be a prefix of l2
        for index in range(1, len(pair[0][1])):
            if pair[0][1][index:] == pair[1][1][:len(pair[0][1]) - index]:
                word1 = pair[0][1][:index] + pair[1][2]
                word2 = pair[0][2] + pair[1][1][len(pair[0][1]) - index:]
                # Prefix language is (L2 / pair[0][1][:index]) \cap L1
                prefixes = copy.deepcopy(pair[1][0])
                prefixes = quotient(prefixes, singFSA(alphabet, pair[0][1][:index]))
                prefixes = intersection(prefixes, pair[0][0])
                prefixes = BFS(prefixes)
                if word1 != word2 and len(prefixes.accepts) > 0:
                    p = []
                    while len(word1) > 0 and len(word2) > 0 and word1[0] == word2[0]:
                        p.append(word1.pop(0))
                        del word2[0]
                    if len(p) > 0:
                        prefixes = concatenation(prefixes, singFSA(prefixes.alphabet, p))
                    vprint3('Adding equation', [prefixes, word1, word2])
                    lprint3('Adding equation', [prefixes, word1, word2])
                    Unresolved.append([prefixes, word1, word2])

def PrePairCheck(PrePairs, Unresolved, alphabet, Everything, Rules):
    # This function checks for prefix critical pairs,
    # That is, instances where rewriting early in the word prevents a rewrite later
    # This leads to ambiguity based on the order of rewriting: we have either LHS can rewrite to RHS, or LHS cannot rewrite to RHS
    # So, after appropriate prefixes (namely the ones that the early rewrite prevented the later rewrite on), we have LHS = RHS as an unoriented equality
    while len(PrePairs) > 0:
        pair = PrePairs.pop()
        pair[0] = Rules[pair[0]]
        pair[1] = Rules[pair[1]]
        vprint3('Checking for prefix critical pairs between', pair[0], 'and', pair[1])
        lprint3('Checking for prefix critical pairs between', pair[0], 'and', pair[1])
        # We're looking for (L1^2 \cap D*)(l_1, r_1)D* \cap (L2, Complement(L2)) to be nonempty.
        prefixes = copy.deepcopy(pair[0][0])
        prefixes = product(prefixes, prefixes)
        prefixes = intersection(prefixes, diagonal(alphabet))
        prefixes = concatenation(prefixes, product(singFSA(alphabet, pair[0][1]), singFSA(alphabet, pair[0][2])))
        prefixes = concatenation(prefixes, diagonal(alphabet))
        prefixes = intersection(prefixes, product(pair[1][0], complement(pair[1][0])))
        # We project onto coordinate 1 because after rewriting l1 -> r1 we are in that coordinate.
        prefixes = projection(prefixes, [1])
        if len(prefixes.accepts) > 0:
            word1 = copy.copy(pair[1][1])
            word2 = copy.copy(pair[1][2])
            p = []
            while len(word1) > 0 and len(word2) > 0 and word1[0] == word2[0]:
                p.append(word1.pop(0))
                del word2[0]
            if len(p) > 0:
                prefixes = concatenation(prefixes, singFSA(prefixes.alphabet, p))
            vprint3('Adding equation', [prefixes, word1, word2])
            lprint3('Adding equation', [prefixes, word1, word2])
            Unresolved.append([prefixes, word1, word2])

def FindDescendents(equation, Rules):
    # Here we're finding all of the irreducible words from either side of equation.
    irreducibles = []
    checked = []
    toBeChecked = [[equation[0], equation[1]], [equation[0], equation[2]]]
    while len(toBeChecked) > 0:
        [lang, word] = toBeChecked.pop()
        if len(lang.accepts) == 0:
            continue
        checked.append([lang, word])
        for rule in Rules:
            for index in range(0, len(word) - len(rule[1]) + 1):
                if word[index: index + len(rule[1])] == rule[1]:
                    prefixes = intersection(concatenation(lang, singFSA(lang.alphabet, word[:index])), rule[0])
                    prefixes = quotient(prefixes, singFSA(lang.alphabet, word[:index]))
                    lang = intersection(lang, complement(prefixes))
                    newWord = word[:index] + rule[2] + word[index + len(rule[1]):]
                    for pair in toBeChecked:
                        if pair[1] == newWord:
                            prefixes = intersection(prefixes, pair[0])
                    for pair in checked:
                        if pair[1] == newWord:
                            prefixes = intersection(prefixes, pair[0])
                    if len(prefixes.accepts) > 0:
                        toBeChecked.append([prefixes, newWord])
        if len(lang.accepts) > 0:
            irreducibles.append([lang, word])
    return irreducibles

def EqualityResolution(Unresolved, Rules, alph, ordering, IntPairs, ExtPairs, PrePairs):
    # This function sorts unoriented equalities into rules
    # Then it adds pairs to check for critical pairs
    newUnresolved = []
    while len(Unresolved) > 0:
        equation = Unresolved.pop()
        vprint3('Working on equation: ', equation)
        lprint3('Working on equation: ', equation)
        # equation is a triple of a language, a word, and another word
        # We need to find all of the descendents of both words after the language,
        irreducibles = FindDescendents(equation, Rules)
        vprint3('Orienting', len(irreducibles), 'irreducibles')
        lprint3('Orienting', len(irreducibles), 'irreducibles')
        # then for each pair of irreducible languages,
        while len(irreducibles) > 0:
            [lang, word] = irreducibles.pop()
            vprint4('Orienting', [lang, word], 'against multiple items')
            lprint4('Orienting', [lang, word], 'against multiple items')
            for index in range(0, len(irreducibles)):
                lang1 = copy.deepcopy(lang)
                word1 = copy.deepcopy(word)
                [lang2, word2] = copy.deepcopy(irreducibles[index])
                vprint4('Against', [lang2, word2])
                lprint4('Against', [lang2, word2])
                if word1 == word2:
                    continue
                inter = intersection(lang1, lang2)
                if len(inter.accepts) == 0:
                    continue
# Commented but left in because this is *bad* for monoids.
# It works for groups, but in monoids ua = va doesn't necessarily imply u = v
# Presumably this is also relevant to keep in mind for term rewriting
#                while len(word1) > 0 and len(word2) > 0 and word1[-1] == word2[-1]:
#                    del word1[-1]
#                    del word2[-1]
                p = []
                while len(word1) > 0 and len(word2) > 0 and word1[0] == word2[0]:
                    p.append(word1.pop(0))
                    del word2[0]
                if len(p) > 0:
                    lang1 = concatenation(lang1, singFSA(lang1.alphabet, p))
                    lang2 = concatenation(lang2, singFSA(lang2.alphabet, p))
                    inter = concatenation(inter, singFSA(inter.alphabet, p))
                (left, right, incomp) = ordering(lang1, lang2, word1, word2, inter)
                # Add new rules and unresolved
                if len(incomp.accepts) > 0:
                    vprint4('Returning unresolved equation', [incomp, word1, word2])
                    lprint4('Returning unresolved equation', [incomp, word1, word2])
                    newUnresolved.append([incomp, word1, word2])
                for rule in Rules:
                    if rule[1] == word1:
                        if rule[2] == word2:
                            right = intersection(right, complement(rule[0]))
                    if rule[1] == word2:
                        if rule[2] == word1:
                            left = intersection(left, complement(rule[0]))
                if len(right.accepts) > 0:
                    for ruleIndex in range(len(Rules)):
                        if len(word1) > len(Rules[ruleIndex][1]):
                            IntPairs.append([ruleIndex, len(Rules)])
                        elif len(word1) < len(Rules[ruleIndex][1]):
                            IntPairs.append([len(Rules), ruleIndex])
                        ExtPairs.append([ruleIndex, len(Rules)])
                        ExtPairs.append([len(Rules), ruleIndex])
                        PrePairs.append([ruleIndex, len(Rules)])
                        PrePairs.append([len(Rules), ruleIndex])
                    ExtPairs.append([len(Rules), len(Rules)])
                    PrePairs.append([len(Rules), len(Rules)])
                    vprint3('Adding rule', [right, word1, word2])
                    lprint3('Adding rule', [right, word1, word2])
                    Rules.append([right, word1, word2])
                if len(left.accepts) > 0:
                    for ruleIndex in range(len(Rules)):
                        if len(word2) > len(Rules[ruleIndex][1]):
                            IntPairs.append([ruleIndex, len(Rules)])
                        elif len(word2) < len(Rules[ruleIndex][1]):
                            IntPairs.append([len(Rules), ruleIndex])
                        ExtPairs.append([ruleIndex, len(Rules)])
                        ExtPairs.append([len(Rules), ruleIndex])
                        PrePairs.append([ruleIndex, len(Rules)])
                        PrePairs.append([len(Rules), ruleIndex])
                    ExtPairs.append([len(Rules), len(Rules)])
                    PrePairs.append([len(Rules), len(Rules)])
                    vprint3('Adding rule', [left, word2, word1])
                    lprint3('Adding rule', [left, word2, word1])
                    Rules.append([left, word2, word1])
    Unresolved = newUnresolved

def EquationCleaning(Rules, Unresolved, alph):
    # We are cleaning up our equations. Anywhere that we can reduce either side of an equation using a rule, we do.
    # This will probably cut the number of internal pairs we have to deal with a bit.
    for rule in Rules:
        for equation in Unresolved:
            index = 0
            while index < len(equation[1]) - len(rule[1]) + 1:
                if rule[1] == equation[1][index: index + len(rule[1])]:
                    p = copy.copy(equation[1][0:index])
                    redlang = intersection(equation[0], quotient(rule[0], singFSA(alph, p)))
                    if len(redlang.accepts) > 0:
                        s = copy.copy(equation[1][index + len(rule[1]):])
                        equation[0] = intersection(equation[0], complement(redlang))
                        Unresolved.append([redlang, p + rule[1] + s, equation[2]])
                        index = 0
                    else:
                        index += 1
                else:
                    index += 1
            index = 0
            while index < len(equation[2]) - len(rule[1]) + 1:
                if rule[1] == equation[2][index: index + len(rule[1])]:
                    p = copy.copy(equation[2][0:index])
                    redlang = intersection(equation[0], quotient(rule[0], singFSA(alph, p)))
                    if len(redlang.accepts) > 0:
                        s = copy.copy(equation[2][index + len(rule[1]):])
                        equation[0] = intersection(equation[0], complement(redlang))
                        Unresolved.append([redlang, equation[1], p + rule[1] + s])
                        index = 0
                    else:
                        index += 1
                else:
                    index += 1
    for i in range(len(Unresolved) - 1, -1, -1):
        if len(Unresolved[i][0].accepts) == 0:
            del Unresolved[i]

def PrunePrefixes(Unresolved, Rules, alph, Everything):
    # This is another form of equation cleanup: we reduce any prefixes that are reducible
    # In particular, for each equation L1: l1 = r1, for each rule L2: l2 -> r2, we want to replace u*l2*v by u*r2*v for all u in L2
    newUnresolved = []
    while len(Unresolved) > 0:
        equation = Unresolved.pop()
        vprint4('Pruning prefixes in equation', equation)
        lprint4('Pruning prefixes in equation', equation)
        for rule in Rules:
            L1byAll = product(equation[0], Everything)
            L2byL2 = product(rule[0], rule[0])
            L2byL2capDStar = intersection(L2byL2, diagonal(alph))
            L2byL2capDStarDot = concatenation(L2byL2capDStar, concatenation(product(singFSA(rule[1]), singFSA(rule[2])), diagonal(alph)))
            L3 = intersection(L1byAll, L2byL2capDStarDot)
            equation[0] = intersection(equation[0], complement(projection(L3, 0)))
            equation[0] = union(equation[0], projection(L3, 1))
            if len(equation[0].accepts) == 0:
                break
        if len(equation[0].accepts) > 0:
            vprint4('Returning equation', equation)
            lprint4('Returning equation', equation)
            newUnresolved.append(equation)
    Unresolved = newUnresolved

def PrefixReductions(Unresolved, Rules, alph):
    # This is a weird one. Basically, we need to do reductions that include a portion of the prefix and a portion of each side of the equality.
    # Okay, so, given an equality L: u = v and a rule P: l -> r, with l = po and u (or v) = os,
    # we can replace L: u = v by the pair of equalities intersection(P, quotient(L, singFSA(alph, p))): rs = pv AND intersection(L, complement(concatenation(P, singFSA(alph, p)))): u = v
    # (Essentially, we prune out what would be a critical pair.)
    newUnresolved = []
    while len(Unresolved) > 0:
        equality = Unresolved.pop()
        vprint3('Reducing prefixes in', equality)
        lprint3('Reducing prefixes in', equality)
        for rule in Rules:
            for index in range(0, len(rule[1])):
                if rule[1][index:] == equality[1][:len(rule) - index]: # overlap with left side of equality
                    # p = rule[1][:index], o = rule[1][index:], s = equality[1][:len(rule) - index]
                    prefixes = intersection(rule[0], quotient(equality[0], singFSA(alph, rule[1][:index])))
                    if len(prefixes.accepts) > 0:
                        word1 = rule[2] + equality[1][:len(rule) - index]
                        word2 = rule[1][:index] + equality[2]
                        while len(word1) > 0 and len(word2) > 0 and word1[-1] == word2[-1]:
                            del word1[-1]
                            del word2[-1]
                        p = []
                        while len(word1) > 0 and len(word2) > 0 and word1[0] == word2[0]:
                            p.append(word1.pop(0))
                            del word2[0]
                        if len(p) > 0:
                            prefixes = concatenation(prefixes, singFSA(prefixes.alphabet, p))
                        vprint3('Returning equality', [prefixes, word1, word2])
                        lprint3('Returning equality', [prefixes, word1, word2])
                        newUnresolved.append([prefixes, word1, word2])
                        equality[0] = intersection(equality[0], complement(prefixes))
                        if len(equality[0].accepts) == 0:
                            break
                if rule[1][index:] == equality[2][:len(rule) - index]: # overlap with right side of equality
                    prefixes = intersection(rule[0], quotient(equality[0], singFSA(alph, rule[1][:index])))
                    if len(prefixes.accepts) > 0:
                        word1 = rule[2] + equality[2][:len(rule) - index]
                        word2 = rule[1][:index] + equality[1]
                        while len(word1) > 0 and len(word2) > 0 and word1[-1] == word2[-1]:
                            del word1[-1]
                            del word2[-1]
                        p = []
                        while len(word1) > 0 and len(word2) > 0 and word1[0] == word2[0]:
                            p.append(word1.pop(0))
                            del word2[0]
                        if len(p) > 0:
                            prefixes = concatenation(prefixes, singFSA(prefixes.alphabet, p))
                        vprint3('Returning equality', [prefixes, word1, word2])
                        lprint3('Returning equality', [prefixes, word1, word2])
                        newUnresolved.append([prefixes, word1, word2])
                        equality[0] = intersection(equality[0], complement(prefixes))
                        if len(equality[0].accepts) == 0:
                            break
        if len(equality[0].accepts) > 0:
            vprint3('Returning equality', equality)
            lprint3('Returning equality', equality)
            newUnresolved.append(equality)
    Unresolved = newUnresolved


def ruleLengthProblem(maxRuleLength, Unresolved):
    # Checks for any rules that are too long
    for equality in Unresolved:
        if len(equality[1]) > maxRuleLength:
            return True
        if len(equality[2]) > maxRuleLength:
            return True

def autostackableNormalForms(group):
    # Gives the normal forms of a group with an autostackable structure.
    if not hasattr(group, 'autostackableStructure'):
        return None
    if not group.autostackableStructure.isConvergent:
        return None
    ev = FSA.allFSA(group.generators)
    nf = FSA.allFSA(group.generators)
    for rule in group.autostackableStructure.Rules:
        # Useful note: If we swap the order in the next line, we have a race condition. Presumably because the computer grabs nf before it can be rewritten.
        nf = intersection(complement(concatenation(concatenation(rule[0], singFSA(group.generators, rule[1])), ev)), nf)
    return nf

def pKB(group, maxRuleNumber = 1000, maxRuleLength = None, maxTime = 600, verbosity = [0, 1], printing = True, logging = ''):
    # Implements prefix-Knuth-Bendix
    # maxTime is the maximum time before the program throws a fit, in seconds.
    # Note that all of the halting conditions can be passed; we only check if we should stop early between passes
    # (Where one pass checks for one type of critical pair, then attempts to orient equalities)
    global vprint0
    global vprint1
    global vprint2
    global vprint3
    global vprint4
    global lprint0
    global lprint1
    global lprint2
    global lprint3
    global lprint4
    # All of these vprints and lprints are verbosity filters. vprints go to console, lprints to log.
    if logging:
        log = open(logging, mode = 'w')
        log.close()
    if 0 in verbosity:
        if printing:
            vprint0 = print
        else:
            vprint0 = lambda *a: None
        if logging:
            def lprint0(*a):
                with open(logging, mode = 'a') as log:
                    for arg in a:
                        log.write(str(arg))
                        log.write(' ')
                    log.write('\n')
        else:
            lprint0 = lambda *a: None
    else:
        vprint0 = lambda *a: None
        lprint0 = lambda *a: None
    if 1 in verbosity:
        if printing:
            vprint1 = print
        else:
            vprint1 = lambda *a: None
        if logging:
            def lprint1(*a):
                with open(logging, mode = 'a') as log:
                    for arg in a:
                        log.write(str(arg))
                        log.write(' ')
                    log.write('\n')
        else:
            lprint1 = lambda *a: None
    else:
        vprint1 = lambda *a: None
        lprint1 = lambda *a: None
    if 2 in verbosity:
        if printing:
            vprint2 = print
        else:
            vprint2 = lambda *a: None
        if logging:
            def lprint2(*a):
                with open(logging, mode = 'a') as log:
                    for arg in a:
                        log.write(str(arg))
                        log.write(' ')
                    log.write('\n')
        else:
            lprint2 = lambda *a: None
    else:
        vprint2 = lambda *a: None
        lprint2 = lambda *a: None
    if 3 in verbosity:
        if printing:
            vprint3 = print
        else:
            vprint3 = lambda *a: None
        if logging:
            def lprint3(*a):
                with open(logging, mode = 'a') as log:
                    for arg in a:
                        log.write(str(arg))
                        log.write(' ')
                    log.write('\n')
        else:
            lprint3 = lambda *a: None
    else:
        vprint3 = lambda *a: None
        lprint3 = lambda *a: None
    if 4 in verbosity:
        if printing:
            vprint4 = print
        else:
            vprint4 = lambda *a: None
        if logging:
            def lprint4(*a):
                with open(logging, mode = 'a') as log:
                    for arg in a:
                        log.write(str(arg))
                        log.write(' ')
                    log.write('\n')
        else:
            lprint4 = lambda *a: None
    else:
        vprint4 = lambda *a: None
        lprint4 = lambda *a: None
    # We'll assume that the ordering is stored in group.ordering. I trust the user, because the user is likely me at this point.
    # We should also check if there's partial progress on a rewriting system.
    # Initial step:
    startTime = time.time()
    Everything = FSA.allFSA(group.generators)
    if hasattr(group, 'autostackableStructure'):
        if group.autostackableStructure.isConvergent:
            return None # We already have an autostackable structure; we're done
        else: # We have a partial but incomplete solution.
            Rules = group.autostackableStructure.Rules
            # It may be worth tossing Rules into Unresolved?
            # No, that's slightly silly. On a genuine ordering change, user should also clean the group's autostackable structure.
            IntPairs = group.autostackableStructure.IntPairs
            ExtPairs = group.autostackableStructure.ExtPairs
            PrePairs = group.autostackableStructure.PrePairs
            Unresolved = group.autostackableStructure.Unresolved
    else:
        Rules = []
        IntPairs = []
        ExtPairs = []
        PrePairs = []
        Unresolved = []
        isConvergent = False
        for rel in group.relators:
            Unresolved.append([Everything, rel[0], rel[1]]) # Rules are of the form [L, l, r], meaning that after any word in L, l goes to r
    # Initial step complete. Now we loop between the (critpair check/equality resolution) loop and the (check Unresolved/prefix reduction) loop.
    while True: # This type of loop (where we continue forever and break at a certain condition) is apparently called a "loop and a half"; python, unfortunately, lacks a native "until" loop type.
        # Check for critical pairs
        # Interior as top priority, just because they are quick to check and eliminate things
        # Exterior as a second priority, i.e. todo if there are no pairs that we haven't check for interior pairs. Harder to check, but not as bad as:
        # Prefix as a bottom priority. THese are *slow* to check, since it's all about constructing FSAs.
        if len(IntPairs) > 0:
            vprint1('Checking ', len(IntPairs), ' pairs of rules for interior critical pairs.')
            lprint1('Checking ', len(IntPairs), ' pairs of rules for interior critical pairs.')
            IntPairCheck(IntPairs, ExtPairs, PrePairs, Unresolved, group.generators, Rules)
        elif len(ExtPairs) > 0:
            vprint1('Checking ', len(ExtPairs), ' pairs of rules for exterior critical pairs.')
            lprint1('Checking ', len(ExtPairs), ' pairs of rules for exterior critical pairs.')
            ExtPairCheck(ExtPairs, Unresolved, group.generators, Rules)
        elif len(PrePairs) > 0:
            vprint1('Checking ', len(PrePairs), ' pairs of rules for prefix critical pairs.')
            lprint1('Checking ', len(PrePairs), ' pairs of rules for prefix critical pairs.')
            PrePairCheck(PrePairs, Unresolved, group.generators, Everything, Rules)
        # Equality resolution
        vprint2('Rules are', Rules)
        lprint2('Rules are', Rules)
        vprint1('Resolving ', len(Unresolved), ' critical pairs.')
        lprint1('Resolving ', len(Unresolved), ' critical pairs.')
        EqualityResolution(Unresolved, Rules, group.generators, group.ordering, IntPairs, ExtPairs, PrePairs)
        # We've run the equality resolution; need to now check if Unresolved is empty, and do prefix resolution step if not
        # The logic here could almost certainly be made more efficient. I expect that prefix resolution is slow, and doing it less often would likely be preferable.
        # But I'm forcing myself to remember that this is proof of concept, not finished product. Efficiencies can be made later.
        if len(Unresolved) > 0:
            vprint1('Pruning and reducing ', len(Unresolved), ' unresolved critical pairs.')
            lprint1('Pruning and reducing ', len(Unresolved), ' unresolved critical pairs.')
            EquationCleaning(Rules, Unresolved, group.generators)
            PrunePrefixes(Unresolved, Rules, group.generators, Everything)
            oldUnresolved = copy.deepcopy(Unresolved)
            PrefixReductions(Unresolved, Rules, group.generators)
            # Okay, we also need a break condition here; in particular, we should break if:
            # There were no prefix reductions to be made
            # This is a simple solution, but not at all elegant. I'm pretty sure it's gonna be memory-heavy.
            if Unresolved == oldUnresolved:
                break
            del oldUnresolved
        # And now we check if we need to halt.
        if len(Unresolved) == 0:
            if len(IntPairs) + len(ExtPairs) + len(PrePairs) == 0: # i.e., every equality has been resolved, after checking that there are no critical pairs left to check
                vprint0('Stopping now. Everything converges!')
                lprint0('Stopping now. Everything converges!')
                isConvergent = True
                break
        # If we have too many rules
        if len(Rules) > maxRuleNumber:
            vprint0('Stopping now. There are too many rules!')
            lprint0('Stopping now. There are too many rules!')
            break
        # If we've spent too much time
        if time.time() - startTime > maxTime:
            vprint0('Stopping now. This is taking too long!')
            lprint0('Stopping now. This is taking too long!')
            break
        # If equalities are too long to compare
        if ruleLengthProblem(maxRuleLength, Unresolved):
            vprint0('Stopping now. The rules are getting too long!')
            lprint0('Stopping now. The rules are getting too long!')
            break
    # Okay, we've stopped. Now we need to update group appropriately.
    AS = AutostackableStructure(isConvergent, Rules, IntPairs, ExtPairs, PrePairs, Unresolved)
    group.autostackableStructure = AS
    vprint0('Total time taken:', time.time() - startTime, 'seconds')
    lprint0('Total time taken:', time.time() - startTime, 'seconds')
