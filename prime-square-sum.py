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
import gc
#import argparse

# Alright since I may have to do this over many days or I may want to break it up over several
# computers, the best way to accomplish this it would seem is to:
# sum (upper bound), (start), Prime[x]^2
# The problem with this though is I need all previous values to then sum against the new prime
# Well not necessarily. I can have one computer summing from say
#
#   sum (4), (1), Prime[x]^2   = 87
#
# Then another just summing from:
#
#   sum (6), (5), Prime[x]^2   = 290
#
# Once I finish the lower bound I can just add that result to the upper. With this type of
# approach I can periodically just grab (lower) + (upper) and say is it greater than (target)?
# If it is I know I've gone too far. Rather than having to recalculate the entire thing. It
# would be nice to have (upper) broken up in to chunks stored in a list. A tree based approach
# would probably work nicely i.e.
#
#   01:  2^2 = 4     sum: 4
#   02:  3^2 = 9     sum: 13
#   03:  5^2 = 25    sum: 38
#   04:  7^2 = 49    sum: 87
#   05:  11^2 = 121  sum: 208
#   06:  13^2 = 169  sum: 377,   partial sum: 169
#   07:  17^2 = 289  sum: 666,   partial sum: 458
#   08:  19^2 = 361  sum: 1027,  partial sum: 819
#   09:  23^2 = 529  sum: 1556,  partial sum: 1348
#   10:  29^2 = 841  sum: 2397,  partial sum: 2189
#
# Now lets imagine I have one computer running 1-5, and another computer running 6-10. In all
# instances the higher component will eclipse the lower by a significant margin if I do it in
# halves. For example row 10 has a partial sum of 2189 and a whole sum of 2397. The difference
# will always be constant.
#
# It would be nice to calculate a rough growth function so I could do an approximation of whether
# or not I'm over the provided value. However, what I can say is that the previous _total_ sum
# will be somewhere between partial sum #1 and #2. 
#
# So, I always want to retain the first two partial sums (or total sums). This will allow me to
# calculate how much extra to potentially add on. Similarly I should only ever need to keep
# 3 top end sums. This should give me enough to work with due to error margin for the low-end
# value. Meaning I can then calculate how much I went above and how much I would go below a
# given target. 
#
#
#TODO: Create a multi-threaded version that just reads from a pipe, looking for primes?
#      This approach would be particularly useful because then I really could have it broken up.
#      One computer that just computes primes. Then another that just squares and sums. However
#      network latency may eventually become the bottleneck. Might be worth testing.

def usage(error, msg=''):
    """
    Print the usage, an error message, then exit with an error
    """
    PrintUsage()
    print >>sys.stderr, globals()['__doc__']
    print >>sys.stderr, error

    sys.exit(1)


def signal_handler(signal, frame):
    global p
    global fAppend
    if(fAppend == True):
        WriteFile()
    print "Count is:\t {0}".format(count)
    if(p != []):
        print "p[-1] is:\t {0}".format(p[-1])
    Report()
    

def PrintUsage():
    print """
Usage: prime-square-sum.py {-w write-file} {-f read-file} {-s start prime-block} {-i increment} {-p last-partialsum}
                            [target] [start] {end}

  Calculates summation of Prime[n]^2 to target number or [end] prime count.
  
  Examples:
    prime-square-sum 666 1 7
    
    prime-square-sum -f allmil.dat -i 100 \
        37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290 1 50000000
    
    prime-square-sum -f 41to50mil.dat -i 100 -p 7752698498499599261971299 \
        37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290 40000000 50000000
"""   


def Report():
    global s
    global l
    global a_target
    lcount = 0
    
    if(s[0][0] != None and l[0][0] != None):
        print '\t\t_Prime_, \t_Square_, \t_Partial-Sum_,\t _count_\n'
        print 'Initial vals:'
        for x in s:
            print '\ts[{0}] = {1:10d},\t{2:10d},\t{3:10d},\t{4:10d}'.format(lcount, x[0], x[1], x[2], x[3])
            lcount += 1
        print '\n\nEnd vals:'
        lcount = 0
    
        for x in l:
            print '\tl[{0}] = {1:10d},\t{2:10d},\t{3:10d},\t{4:10d}'.format(lcount, x[0], x[1], x[2], x[3])
            lcount += 1
        
        print '\n\nSynopsis:'
        print '\n\t{0:10d} == {1:10d}, {2}'.format(a_target, l[2][2], "true" if a_target == l[2][2] else "false")
        
    print '\n\n__________________________\n\n'



#public static BitSet computePrimes(int limit)
#{
#    final BitSet primes = new BitSet();
#    primes.set(0, false);
#    primes.set(1, false);
#    primes.set(2, limit, true);
#    for (int i = 0; i * i < limit; i++)
#    {
#        if (primes.get(i))
#        {
#            for (int j = i * i; j < limit; j += i)
#            {
#                primes.clear(j);
#            }
#        }
#    }
#    return primes;
#}



##############################################

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


def power_mod(a, b, n):
    """
power_mod(a,b,n) --> int

Return (a ** b) % n
"""
    if b < 0:
        return 0
    elif b == 0:
        return 1
    elif b % 2 == 0:
        return power_mod(a*a, b/2, n) % n
    else:
        return (a * power_mod(a,b-1,n)) % n

    
def rabin_miller(n, tries = 7):
    """
rabin_miller(n, tries) --> Bool

Return True if n passes Rabin-Miller strong pseudo-prime test on the
given number of tries, which indicates that n has < 4**(-tries) chance of being composite; return False otherwise.

http://mathworld.wolfram.com/Rabin-MillerStrongPseudoprimeTest.html
"""
    if n == 2:
        return True
    
    if n % 2 == 0 or n < 2:
        return False
    
    p = primes(tries**2)

    # necessary because of the test below
    if n in p:
        return True
    sn = str(n)
    fsn = 0
    
    #Fadic compression
    for x in sn:
        if(fsn + int(x) >= 10):
            fsn += 1
        fsn = (fsn + int(x)) % 10
    
    #Fadic base-10 values mod 3 are divisible by 3, 6, and/or 9
    if(fsn % 3 == 0):
        return False
        
    s = n - 1
    r = 0
    while s % 2 == 0:
        r = r+1
        s = s/2
        
    for i in range(tries):
        a = p[i]
        
        if power_mod(a,s,n) == 1:
            continue
        else:
            for j in range(0,r):
                if power_mod(a,(2**j)*s, n) == n - 1:
                    break
            else:
                return False
            continue
    return True

#def Prime(n):
"""
Return nth Prime starting from 1, 0 is error.
"""
 #   for

#def PrimeQ(n):
"""
Similar to Mathematica functionality.
"""





##############################################

def ReadFile(filename):
    global p
    fReadFile = None
    error = False
    
    try:
        fReadFile = open(filename, 'rb+' )
    except IOError:
        error = True
        print "Error: opening {0}".format(filename)
    if(error == False):
        error = False
        lcount = 0
        pn = []
        while error == False:
            try:
                if lcount == 0:
                    p = pickle.load(fReadFile)
                else:
                    pn = pickle.load(fReadFile)
                lcount += 1
            except:
                print "Copied in {0} loads from {1}...".format(lcount, filename)
                error = True
                
            if(error != True):
                for i in pn:
                    p.append(i)
                
        fReadFile.close()
    gc.collect()

    
    
    #for lines in fReadFile.readlines():
    #    p.append(long(lines))

 
def WriteFile():
    error = False
    global fWriteFileArg
    global fAppend
    global p
    
    fWriteFile = None
    
    if(fAppend == True and fWriteFileArg != None):
        try:
            fWriteFile = open(fWriteFileArg, 'wb+' )
        except IOError:
            error = True
            print "Error: opening {0}".format(fWriteFileArg)
        
        if(error != True):
            #Byte-packing is the last option hence (-1). For better
            #readability use 0 (primes are then human readable)
            pickle.dump(p, fWriteFile, -1)
            fWriteFile.close()


##############################################

 #argv=None   
def Main():
    
    #if argv is None:
    #    argv = sys.argv
    

    global count
    global s
    global l
    global p
    global a_startsize
    global a_increment
    global a_target
    global a_min
    global a_max
    global a_partialsum

    result = 0
    partialsum = 0
    p_small = []

    if(p == []):
        if(a_startsize == 0):
            #original 10000
            p = primes( 10000 if (a_target > 100000) else a_target )
        else:
            p = primes(a_startsize)
    else:
        if(a_partialsum > 0 and a_min > 1):
            count = a_min
            partialsum = a_partialsum
    
    ref = [p]
    
    while(partialsum < a_target and (a_max == -1 or a_max > count)):
        if(count > 0 and s[0][0] != None):
            p_small = []
            primegap = 0
            while(p_small == []):
                primegap += 1
                #If p_small is [] then the prime_gap has grown so wide we're
                #getting no new primes, so increment needs to be enlarged
                a_increment *= primegap
                p_small = primes(a_increment, ref, p[-1])
                #When len of p_small is only 2 units double a_increment. Should
                #prevent scenario of needing primegap. 
                if(len(p_small) <= 2):
                    a_increment *= 2
                p = ref[0]
        
        if(p_small == []):
            p_small = p
    
        #Random idea: Maybe do a compounding function that iterates over all these values a 2nd/3rd/nth time?
        #I.e. take all the old values and sum them over and over again.
        for i in p_small:
            count += 1
            result = i**2
            partialsum = partialsum + result
            
            #Comical that I'm having a bug that occurs between 217 & 218. Pretty close to Pi's
            #216 error. Actually it breaks right after prime 216 (base-0) -> 1327.
            #Figured it out. Prime[218]-Prime[217] = 34. I was providing an increment of 32
            #So the primes() func was returning no p_small
            
            #if(count >= 217):
                #print (partialsum)
                #assert (partialsum == 116747412)
                
            if(count <= (a_min+2)):
                index = (count-a_min)-1
                s[index][0] = i
                s[index][1] = result
                s[index][2] = partialsum
                s[index][3] = count
            elif(count >= (a_min+3) and count < (a_min+6)):
                index = (count-a_min)-3
                l[index][0] = i
                l[index][1] = result
                l[index][2] = partialsum
                l[index][3] = count
            elif(count >= (a_min+6)):
                for x in range(0,4):
                    l[0][x] = l[1][x]
                    l[1][x] = l[2][x]
                    
                l[2][0] = i
                l[2][1] = result
                l[2][2] = partialsum
                l[2][3] = count
                
            if (partialsum >= a_target):
                break;

    WriteFile()
    Report()

    #wrapper = [p]
    #primes(200, wrapper)
    #print wrapper[0][-1]
    #rabin_miller(97)
    #rabin_miller(2179)




############################################


try:
    opts, args = getopt.getopt(sys.argv[1:], 'hf:s:i:w:p:', ['help', 'file=', 'start=', 'increment=', 'write=', 'partialsum='])
except getopt.error, msg:
    usage(1, msg)

p = []
a_startsize = 0
a_increment = 100
a_highestReadPrime = -1
a_partialsum = 0
fWriteFileArg = None
fReadFileArg = None
fAppend = False

#[-w write primes to file] [-f primes-list or file] [-s prime-block start] [-i prime-block increment] [target] [start] {end}

for opt, arg in opts:
    if opt in ('-h', '--help'):
        usage(0)
        
    elif opt in ('-f', '--file'):
        fReadFileArg = arg
        ReadFile(fReadFileArg)
            
    elif opt in ('-w', '--write'):
        fAppend = True
        fWriteFile = None
        error = False
        try:
            fWriteFileArg = arg
            fWriteFile = open(fWriteFileArg, 'wb+' )
        except IOError:
            error = True
            print "Error: opening {0}".format(arg)
            fAppend = False
        
        if(error == False):
            fWriteFile.close()
    
    elif opt in ('-s', '--start'):
        a_startsize = long(arg)
        
    elif opt in ('-i', '--increment'):
        a_increment = long(arg)
        
    elif opt in ('-p', '--partialsum'):
        a_partialsum = long(arg)
    #argv.remove(opt)
    #argv.remove(arg)
 
#   Only necessary if I want to read and write to the same file (probably not wise if
#   make ctrl+c write data too.
#if(fAppend == false and fReadFile != None):
#    fReadFile.close()
    
if(len(args) < 2 or len(args) > 4): #fix inequality to <
    usage(0)
    exit(1)
    
a_target = long(args[0])
a_min = long(args[1])
if(len(args) == 3):
    a_max = long(args[2])
else:
    a_max = -1         
    
count = long(0)

s = [[None, None, None, None],
    [None, None, None, None]]
        
l = [None]*3
for i in range(3):
    l[i] = [None]*4
    
signal.signal(signal.SIGINT, signal_handler)

Main()