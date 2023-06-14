#####
# Coxeter Group Prefix Knuth-Bendix File
# Coded by Ash DeClerk (declerk.gary@huskers.unl.edu)
# Most recently updated 6/5/2021
#####

"""
This file is intended to search for an autostackable structure for the Coxeter group on four generators, where each generator is part of exactly one relator of length 6.
(A presentation is given below, of course.)
We're starting out by attempting to use regular-split shortlex. The plan, at time of writing, is to attempt a variety of FSAs for the splitting automaton, and hope that one of them works.
I think the natural FSA to use is essentially the Coxeter diagram -- and that may be my thought for *all* Coxeter groups. The ordering on each vertex is up for debate, though.
The three most sensible options are:
    cyclically permute the letters so that the most recent letter is at the front (attempting now, it worked?!?!?! It wasn't supposed to work!);
    move the most recent letter to the front while leaving the relative order of the rest; or
    keep a and d together, and b and c together, and permute such that the most recent letter is in the front half of the alphabet.
"""

import prefixKnuthBendix as prefixKnuthBendix
import FSA
import orderAutomata


if __name__ == "__main__":
    Cox = prefixKnuthBendix.Group({'a', 'b', 'c', 'd'}, [[['a','a'],[]], [['b','b'],[]], [['c','c'],[]], [['d', 'd'],[]],
                                                         [['a','d', 'a'], ['d', 'a', 'd']], [['b','c','b'],['c', 'b', 'c']],
                                                         [['a', 'b', 'a', 'b'], ['b', 'a', 'b', 'a']],
                                                         [['a', 'c', 'a', 'c'], ['c', 'a', 'c', 'a']],
                                                         [['b', 'd', 'b', 'd'], ['d', 'b', 'd', 'b']],
                                                         [['c', 'd', 'c', 'd'], ['d', 'c', 'd', 'c']]])

    # Make the FSA
    alph = {'a', 'b', 'c', 'd'}
    memLast = FSA.FSA(4, {0}, alph, {'a': [0, 0, 0, 0], 'b': [1, 1, 1, 1], 'c': [2, 2, 2, 2], 'd': [3, 3, 3, 3]})
    ordAut = orderAutomata.RegSplitSlex(memLast, {0: ['a', 'b', 'c', 'd'], 1: ['b', 'c', 'd', 'a'], 2: ['c', 'd', 'a', 'b'], 3: ['d', 'a', 'b', 'c']})
    diag = FSA.diagonal(alph)

    def ordering(lang1, lang2, word1, word2, inter):
        # we need to orient the intersection
        # The prefixes where left is smaller than right
        left = FSA.product(lang2, lang1)
        left = FSA.intersection(left, diag)
        left = FSA.concatenation(left, FSA.product(FSA.singFSA(alph, word2), FSA.singFSA(alph, word1)))
        left = FSA.intersection(left, ordAut)
        left = FSA.projection(left, [0])
        left = FSA.BFS(FSA.quotient(left, FSA.singFSA(alph, word2)))
        # The prefixes where right is smaller than left
        right = FSA.product(lang1, lang2)
        right = FSA.intersection(right, diag)
        right = FSA.concatenation(right, FSA.product(FSA.singFSA(alph, word1), FSA.singFSA(alph, word2)))
        right = FSA.intersection(right, ordAut)
        right = FSA.projection(right, [0])
        right = FSA.BFS(FSA.quotient(right, FSA.singFSA(alph, word1)))
        # The prefixes where left and right are incomparable
        incomp = FSA.intersection(FSA.intersection(inter, FSA.complement(left)), FSA.complement(right))
        return (left, right, incomp)

    Cox.ordering = ordering

    prefixKnuthBendix.pKB(Cox, maxTime = 1200)
