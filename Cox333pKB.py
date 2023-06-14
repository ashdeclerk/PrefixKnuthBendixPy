#####
# Coxeter 3,3,3 Prefix Knuth-Bendix Test File
# Coded by Ash DeClerk (declerk.gary@huskers.unl.edu)
# Most recently updated 6/5/2021
#####

import prefixKnuthBendix
import FSA
import orderAutomata

Cox333 = prefixKnuthBendix.Group({'a', 'b', 'c'}, [[['a','a'],[]], [['b','b'],[]], [['c','c'],[]], [['a','b', 'a'], ['b', 'a', 'b']], [['a','c','a'],['c', 'a', 'c']], [['b', 'c', 'b'], ['c', 'b', 'c']]])

# Make the FSA
alph = {'a', 'b', 'c'}
transitions = {'a': [1, 2, 0], 'b': [0, 1, 2], 'c': [0, 1, 2]}
mod3a0 = FSA.FSA(3, {0}, alph, transitions )
ordAut = orderAutomata.RegSplitSlex(mod3a0, {0: ['a', 'b', 'c'], 1: ['b', 'c', 'a'], 2: ['c', 'a', 'b']})
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

Cox333.ordering = ordering

prefixKnuthBendix.pKB(Cox333, maxTime = 20)#, verbosity = [0, 1, 3], logging = 'Cox333.txt', printing = False)
