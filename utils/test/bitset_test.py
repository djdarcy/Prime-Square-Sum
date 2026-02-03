#!/usr/bin/env python

import bitset
import math

def pi(n):
    return n / math.log(n)

limit = 1000000
bitarray = bitset.Bitset(0, 10) #1024*10
bitarray[4:9] = True
bitarray[0:1] = False
bitarray[2:limit] = True

for i in range(0, limit, 1):
    if (bitarray[i]):
        for j in range(i*i, limit, i):
        #for (int j = i * i; j < limit; j += i)
            #print bitarray[j]
            bitarray.clear(j)
            #print bitarray[j]
            #bitarray[j] = True
            #print bitarray[j]


#return primes;
count = 0
#for bit in bitarray:
#    if(bit == True):
#        
#    count += 1