#!/usr/bin/env python

#34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216 <
#   37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290
# is false. (test_exp = 26)
# So, the program should eventually get to this number (in many years =)

test_exp = 2
test = long(1)

while(True):
    print test
    test *= long(2**test_exp)
    test_exp += 1