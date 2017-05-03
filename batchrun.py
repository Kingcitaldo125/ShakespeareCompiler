#!/usr/bin/env python3

import subprocess
import os
import glob
import pprint

def sf(x):
    i=x.find(".")
    assert i!=-1
    x=x[1:i]
    return int(x)
    
def main(): 
    global expected   
    ofp=open("batchresults.txt","w")
    files=glob.glob("t*.txt")
    files.sort(key=sf)

    stderr=open("x","w+b")
    stdout=open("z","w+b")
    stdin=open("y","w+b")
    stdin.write(b"2\n3\n4\n5\n")
    stdin.flush()

    Q={}

    mismatches=[]
    
    for f in files:
        print(f)
        
        line = open(f).readline()
        line=line.lower()
        if "incorrect" in line:
            correct=False
            type_='I'
        elif "correct" in line:
            correct=True
            type_='C'
        else:
            print("Don't know if",f,"is correct or not")
            assert 0
     
        if "crash" in line:
            crashes=True
            type_='X'
        else:
            crashes=False
            
        print("~~~~~~~~~~"+f+" ["+type_+"]~~~~~~~~~~",file=ofp)

        stderr.seek(0)
        stderr.truncate()
        rv = subprocess.call([
        
        
            #replace this with the command to compile your code
            "python","main.py",f
            
            
            ],
            stderr=stderr
        )
        
        if rv != 0:
            if not correct:
                stderr.seek(0)
                msg=stderr.read()
                ofp.write(msg.decode())
                ofp.write("\n")
            else:
                print("Failed on apparently correct program",f)
                assert 0
        else:
            if not correct:
                print("Succeeded on apparently incorrect program",f)
                assert 0
            else:
                stdin.seek(0)
                stdout.seek(0)
                stdout.truncate()
                stderr.seek(0)
                stderr.truncate()
                rv = subprocess.call([
                
                    #replace this with the command to run your code
                    #"./"+f+".elf"
                    
                    
                    ], stdin=stdin, stdout=stdout,stderr=stderr
                )
                if rv == 0:
                    if crashes:
                        print("Did not crash but it should have")
                        assert 0
                    else:
                        stdout.seek(0)
                        ofp.write(stdout.read().decode())
                        ofp.write("\n")
                        stdout.seek(0)
                        Q[f]=stdout.read().decode()
                        if Q[f] != expected.get(f,"***"):
                            mismatches.append(f)
                else:
                    if not crashes:
                        print("Crashed unexpectedly")
                        stdout.seek(0)
                        print(stdout.read())
                        stderr.seek(0)
                        print(stderr.read())
                        assert 0
                    else:
                        ofp.write("(Crashed: "+str(rv)+")\n")
                        

    ofp.close()
    
    if len(mismatches) != 0:
        print("These outputs had mismatches:",",".join(mismatches))
    else:
        print("Give yourself a cookie!")

    #pprint.pprint(Q)



expected={
 't1.txt': '-1',
 't101.txt': '8420',
 't102.txt': '',
 't108.txt': '',
 't109.txt': '',
 't110.txt': '',
 't111.txt': '',
 't112.txt': '',
 't117.txt': '',
 't118.txt': '',
 't119.txt': '',
 't12.txt': '-4',
 't120.txt': '',
 't121.txt': '',
 't122.txt': '',
 't126.txt': '25081512001221255186',
 't127.txt': '',
 't128.txt': '',
 't130.txt': '',
 't131.txt': 'Hello',
 't132.txt': '',
 't137.txt': '',
 't138.txt': '',
 't140.txt': '',
 't141.txt': '',
 't142.txt': 'A\nEnter a character --> 3\nEnter a number --> 4\n',
 't147.txt': '',
 't148.txt': '',
 't15.txt': '-4',
 't150.txt': '',
 't151.txt': '',
 't152.txt': '',
 't157.txt': '',
 't158.txt': '',
 't16.txt': '8',
 't17.txt': '-2',
 't19.txt': '0-1',
 't26.txt': '-1-1',
 't29.txt': '-3',
 't30.txt': '-1',
 't33.txt': '1',
 't34.txt': '',
 't36.txt': '1',
 't37.txt': '2',
 't38.txt': '-10',
 't39.txt': '070',
 't41.txt': '24',
 't42.txt': '1',
 't48.txt': 'Enter a number --> Enter a number --> 5',
 't49.txt': 'Enter a number --> Enter a number --> Sum\n'
            '5\n'
            'Difference\n'
            '-1\n'
            'Product\n'
            '6\n'
            'Quotient\n'
            '0\n'
            'Remainder\n'
            '2\n'
            'Square\n'
            '4\n'
            'Square ROOT\n'
            '2\n'
            'Twice\n'
            '4\n'
            'Thrice\n'
            '6\n'
            'Half\n'
            '1\n'
            'Both\n'
            '1\n'
            'Either\n'
            '1\n'
            'Opposite\n'
            '0\n'
            '\n',
 't50.txt': 'Y\n',
 't51.txt': 'Y\n',
 't52.txt': 'N\n',
 't53.txt': 'Y\n',
 't54.txt': 'Y\n',
 't55.txt': 'N\n',
 't56.txt': 'N\n',
 't57.txt': 'Y\n',
 't58.txt': 'Y\n',
 't59.txt': 'N\n',
 't60.txt': 'Y\n',
 't61.txt': 'N\n',
 't62.txt': 'Y\n',
 't63.txt': 'N\n',
 't64.txt': 'Y\n',
 't65.txt': 'N\n',
 't71.txt': '1',
 't72.txt': '10\n9\n8\n7\n6\n5\n4\n3\n2\n1\n',
 't73.txt': '0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n',
 't78.txt': '020',
 't80.txt': '0',
 't81.txt': '1',
 't82.txt': '11',
 't83.txt': '1',
 't84.txt': '1',
 't85.txt': '-10',
 't86.txt': '-1-1',
 't87.txt': 'Enter a character --> 3',
 't89.txt': '',
 't90.txt': '',
 't91.txt': '',
 't95.txt': '',
 't97.txt': '',
 't98.txt': ''}

main()
