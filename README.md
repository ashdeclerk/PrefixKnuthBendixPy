# PrefixKnuthBendixPy
This project is an implementation of the prefix-Knuth-Bendix completion procedure, a modification of Knuth-Bendix which is designed to search for autostackable structures (or bounded regular prefix-rewriting systems in monoids more generally). The procedure was designed by Ash DeClerk (that's me, the author of this project!) as part of their Ph.D. dissertation (available at https://digitalcommons.unl.edu/mathstudent/115/, with the relevant results in Chapter 3).

There are currently five pieces of code in this repository:
- prefixKnuthBendix.py is the actual implementation of pKB. The main function that you want to call is all the way at the bottom, pKB(group, maxRuleNumber = 1000, maxRuleLength = None, maxTime = 600, verbosity = [0, 1], printing = True, logging = ''). 
  - group should be a Group object (from early in the prefixKnuthBendix file) with an ordering added to it. This is the only required argument; the rest are optional and have reasonable defaults.
  - maxRuleNumber gives the maximum number of rules before pKB says "no, this is too many rules". By default, this is 1000 rules.
  - maxRuleLength gives the maximum length of either word in a rule before pKB says "no, these are too long", defaulting to not having a maximum length.
  - maxTime gives the maximum time in seconds before pKB says "no, this is taking too long". This isn't the actual maximum run time, since I only have it check after each batch of checking critical pairs and resolving equalities (which can take a while, since it looks at all of the critical pairs of a certain type and tries to resolve all of the unresolved equalities into rules with each batch). By default, this is ten minutes.
  - verbosity indicates what gets printed to console/logging. I don't completely remember what verbosity levels print each thing, but there are levels 0 through 4, which are independent (so having verbosity 4 doesn't force verbosity 2 as well, for example).
  - printing is a boolean; if True (the default), then things do get printed to console.
  - logging is the name of a log file. By default, this is the empty string, which does not make a file to print things. Be careful not to use the name of a file that already exists, because that's going to write a bunch of stuff to the end of the file rather than making a new file with a similar name.
- FSA.py is my package for dealing with finite state automata. An FSA initializes with a number of states, a set of accepting states, the alphabet (as a set), and the transition function.
  - The transition function should be a dictionary where keys are letters of your alphabet. The entries are themselves dictionaries, with keys being states and entries being the target state. That is, transitions[a][q] = delta(q, a).
  - The initial state is 0. This is different from how kb-mag does things, and I remember you warning me that a lot of group theorists would be used to 0 being a fail state.
- orderAutomata.py builds FSAs accepting {(u, v) | v < u (and u and v differ only on a suffix of length at most k, where relevant)}. This is the reverse of how I have things set up in the paper, but matches with how I have code set up elsewhere.
  - Probably the most interesting thing at the moment is RegSplitSlex, which is an implementation of regular-split shortlex. It requires an fsa (from my FSA package) whose alphabet is the alphabet you're interested in, along with a dictionary perms, where keys are states in the FSA and entries are your alphabet as a list, in order from smallest letter at that state to largest letter at that state.
  - Everything else that's currently implemented is compatible with concatenation on both sides, so it would be just as reasonable to use Knuth-Bendix. I've implemented them just to have them for building stuff later.
- Cox333pKBTest.py and Cox443344pKB.py are both samples that actually run pKB on a specific group with a specific ordering (so you should probably use them as a starting point for making your own code). 
  - They start by setting up the group, which has a set of monoid generators and a list of relators (as pairs of words that are equal in the group).
  - Then they set up the ordering. If you have an FSA ordAut that accepts the pairs (u, v) such that v < u, then you don't need to touch the ordering() function at all. If you're doing something different (which I'm trying for BS(1, 2), for example), then you need a function where the inputs are lang1, lang2 (both FSAs), word1, word2 (both words over A), and inter (the intersection of lang1 and lang2), and the outputs are a triple (left, right, incomp) where:
    - left is an FSA accepting the language {p \in inter | p * word1 < p * word2} (i.e. the relevant prefixes where you want to move to the left word),
    - right is an FSA accepting the language {p \in inter | p * word2 < p * word1} (i.e. the relevant prefixes where you want to move to the right word),
    - and incomp is an FSA accepting the language {p \in inter | p * word1 and p * word2 are incomparable}
  - Then they attach the ordering to the group and run pKB.
