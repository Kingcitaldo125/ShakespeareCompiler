#!/usr/bin/env python3

import subprocess
import os
import re
import os.path 

def sf(x):
    i=x.find(".")
    assert i!=-1
    x=x[1:i]
    return int(x)
    
def main(): 

    rex=re.compile(r"^x(\d+).txt$")
    files=[]
    for dirpath,dirnames,filenames in os.walk("."):
        for f in filenames:
            m=rex.match(f)
            if m:
                files.append((int(m.group(1),10),os.path.join(dirpath,f)))
    files.sort()

    compilesucceeded = open("_compilesucceeded.txt","w")
    compilefailed = open("_compilefailed.txt","w")
    runsucceeded = open("_runsucceeded.txt","w")
    runfailed = open("_runfailed.txt","w")
    
    stderr=open("x","w+b")
    stdout=open("z","w+b")
    stdin=open("y","w+b")
    stdin.write(b"2\n3\n4\n5\n")
    stdin.flush()

    for _,f in files:
        print(f)
        stdout.seek(0)
        stdout.truncate()
        rv = subprocess.call([
        
        
            #replace this with the command to compile your code
            "python","main.py",f
            
            
            ],
            stdout=stdout
        )
        
        if rv == 0:
            print(f,file=compilesucceeded)
            print("Succeed")
            stdin.seek(0)
            stdout.seek(0)
            stdout.truncate()
            stderr.seek(0)
            stderr.truncate()
            """rv = subprocess.call([
            
                #replace this with the command to run your code
                "./"+f+".elf"
                
                
                ], stdin=stdin, stdout=stdout,stderr=stderr
            )
            if rv == 0:
                print(f,file=runsucceeded)
                print("\n",file=runsucceeded)
                stdout.seek(0)
                print(stdout.read().decode(),file=runsucceeded)
                print("\n",file=runsucceeded)
            else:
                print(f,file=runfailed)"""
        else:
            print("Fail")
            print(f,file=compilefailed)

    compilesucceeded.close()
    compilefailed.close()
    runsucceeded.close()
    runfailed.close()
    
main()
