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

def ReadFile(outputFilename, inputFilenames):
    
    fWriteFile = None
    for filename in inputFilenames:
        nums = []
        fReadFile = None
        error = False
        re_nums = re.compile("(\s*)") #(\d+)
        try:
            fReadFile = open(filename, 'rb+' )
        except IOError:
            error = True
            print "Error: opening {1}".format(filename)
            return -1
        if(error == False):
            #fReadFile.next()
            #fReadFile.readlines(1)
            fReadFile.readline()
            fReadFile.readline()
            for lines in fReadFile.readlines():
                result = re_nums.split(lines)
                for i in range(1,9):
                    #result = re_nums.split(lines)[2*i]
                    #if(isinstance(result, (int, long, float, complex))):                    
                    nums.append(long(result[2*i]))            
            fReadFile.close()
            
            try:
                if(fWriteFile == None):
                    fWriteFile = open(outputFilename, 'wb+' )
            except IOError:
                error = True
                print "Error: opening {0}".format(outputFilename)
                return -1
            
            if(error != True):
                #Byte-packing is the last option hence (-1). For better
                #readability use 0 (primes are then human readable)
                pickle.dump(nums, fWriteFile, -1)
                print "Finished ... {0}\n".format(filename)

    if(fWriteFile != None):                
        fWriteFile.close()
    return 0
    #return nums

#C:\Users\Extreme\Documents\primes>prime-texttable-to-list.py allmil.dat primes1.txt primes2.txt primes3.txt primes4.txt primes5.txt primes6.txt primes7.txt primes8.txt primes9.txt primes10.txt primes11.txt primes12.txt primes13.txt primes14.txt primes15.txt primes16.txt primes17.txt primes18.txt primes19.txt primes20.txt primes21.txt primes22.txt primes23.txt primes24.txt primes25.txt primes26.txt primes27.txt primes28.txt primes29.txt primes30.txt primes31.txt primes32.txt primes33.txt primes34.txt primes35.txt primes36.txt primes37.txt primes38.txt primes39.txt primes40.txt primes41.txt primes42.txt primes43.txt primes44.txt primes45.txt primes46.txt primes47.txt primes48.txt primes49.txt primes50.txt

args = sys.argv[1:]
outputFilename = args[0]
args.remove(args[0])
    
if (ReadFile(outputFilename, args) > 0):
    print "Failed Conversion"
else:
    print "Successful Conversion from {0} ... to {1}".format(args[0], outputFilename)