#!/usr/bin/env python

import os
import sys
import re
import string
import subprocess
import datetime as dt
import shutil
import math
import signal
import getopt
import pickle
import pprint


def primes(n, list = None, minimum = 0):
    """
primes(n) --> primes

Return list of primes from minimum up to but not including n.  Uses Sieve of Erasth.
If list is given values are returned on the list (with minimum _as_ 0). If minimum
is provided the result is returned, and the full list is returned through the 2nd
param
"""
    
    if n < 2:        
        if list is None:    
            return []
        else:
            list[0] = []
            return
    
    l = 0
    
    if list is None:
        nums = range(3,int(n),2)
    else:
        nums = list[0]
        nums.remove(2)
        l = len(nums)
        n_start = nums[-1]+2    #all num[-1], as primes, should be odd, to get another, +2
        
        if(n-1 <= n_start):
            n2 = n+n_start
        else:
            n2 = n

        for i in range(n_start, n2, 2):
            nums.append(i)
        
        #if(nums[0] == 2):
    
    global p
    p = []
    psmall = []
    
    p.append(2)
    
    while nums:
        new_prime = nums[0]
        p.append(new_prime)
        if( minimum > 0 and new_prime > minimum):
            psmall.append(new_prime)
        
        if(list is None):
            x = 1
        else:
            x = l
            if(l > 1):
                l -= 1
        
        multiple = new_prime * 2
        for i in nums[x:]:
            if multiple > i:
                continue
            if i % new_prime == 0:
                nums.remove(i)

        nums.remove(nums[0])   
    
    #Report();
    if(list is None):
        return p
    else:
        list[0] = p
        #assert( psmall != [])
        return psmall
    
    
    
    
    
    
p = primes(10000)

#Write
output = open('data.pkl', 'wb')
pickle.dump(p, output, -1)
output.close()

#Read
pkl_file = open('data.pkl', 'rb')

data1 = pickle.load(pkl_file)
pprint.pprint(data1)

pkl_file.close()



