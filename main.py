import re

tokens = []
pretokens = []
stringList = []
regexes = []

epsilon = '`'
start_symbol = 0


class Item(object):
    def __init__(self, lhs, rhs, dpos, how, column):
        self.lhs = lhs
        self.rhs = rhs
        self.dpos = dpos
        self.column = column
        self.how = how

    def __str__(self):
        return str(self.lhs)+str(self.rhs)


class Token(object):
    def __init__(self, sym, lex, lnum):
        self.symbol = sym
        self.lexeme = lex
        self.linenumber = lnum

    def __str__(self):
        strr = ""
        strr += "SYMBOL: "
        strr += str(self.symbol)
        strr += " LEXEME: "
        strr += str(self.lexeme)
        strr += " LINE: "
        strr += str(self.linenumber)
        return str(strr)

    def printIdentity(self):
        print("(sym=\""+self.symbol+"\", lexeme=\""+self.lexeme+"\")")


class Grammar(object):
    def __init__(self, txt, terms, nonterms, prods):
        self.text = txt
        self.terminals = terms
        self.nonterminals = nonterms
        self.productions = prods
        self.start = 'S'

    def __str__(self):
        st = ""
        for x in self.text:
            st += '\n'
            st += x
        return st


class Production(object):
    def __init__(self, thing):
        self.thing = thing
        self.dpos = 0
        self.lhs = ""
        self.rhs = ""
        self.rhsString = ""

        statemnt = r"(.+)(\s->\s)(.+)"
        regexx = re.compile(statemnt)

        s = self.thing

        m = regexx.search(s, 0, len(s))
        if m:
            self.lhs = str(m.group(1))
            self.rhs = str(m.group(3))
            self.rhsString = self.rhs

            self.rhs = self.rhs.split(' ')
        else:
            raise TypeError("ERROR! BAD PRODUCTION IN FORM: ", self.thing)

    def __str__(self):
        return str(self.thing)


class TreeNode(object):
    def __init__(self, sym, tok):
        self.sym = sym
        self.token = tok
        self.children = []

    def __str__(self):
        return str(self.sym)

    def prepend_child(self, chile):
        self.children.append(chile)


def tokenize(dotest, debug):
    global pretokens, tokens, stringList, regexes
    LineCounter = 0

    terms = []
    FILE = 0
    if dotest:
        FILE = open("testRegexes.txt")
    else:
        FILE = open("regexes.txt")

    for line in FILE:
        LineCounter += 1

        xx = re.match(r'(.+) -> (.*)', line)
        pretokens.append([xx.group(1), re.compile(xx.group(2))])
        terms.append(xx.group(1))

    #print(LineCounter, "lines in the Regular Expression file.")
    #print(terms)

    # Populate terminals and nonterminals
    nonT = open('terminals.txt', 'w')
    for nn in range(len(terms)):
        nonT.write(terms[nn])
        if nn < len(terms)-1:
            nonT.write(' ')
    nonT.close()

    effr = open('input.txt', 'r+')
    inputString = ""
    for l in effr:
        inputString += str(l)
    lengthofstr = len(inputString)

    #print("Input string:", inputString)

    token_container = []

    i = 0
    line = 1
    while i < lengthofstr:
        for sym, regex in pretokens:
            m = regex.match(inputString, i)
            if m:
                if debug:
                    print(sym)
                if m.start == i or m.start() == i:
                    if sym != "whitespace" and sym != "comments":
                        token_container.append(Token(sym, m.group(0), line))
                    line += m.group(0).count("\n")
                    i = m.end()
                    break
        else:
            errorTok = ""
            for i in range(i, lengthofstr):
                if inputString[i] == ' ' or inputString[i] == '\n' or inputString[i] == '.':
                    break
                if inputString[i] == '!':
                    break
                if inputString[i] == '?':
                    break
                errorTok += inputString[i]
            raise TypeError("ERROR: Cannot match token", errorTok)

    effr.close()
    FILE.close()

    return token_container


def computeNullable(gramm):
    global epsilon

    nullable = set()
    loop_broke = False
    stable = False
    ctr = 0
    xctr = 0

    fexilon = False
    for p in gramm.productions:
        for x in p.rhs:
            if x == epsilon:
                fexilon = True
                c = set([p.lhs])
                nullable = nullable.union(c)
                # print(nullable)
                break

    # If lambda does not exist in any production -> return
    if not fexilon:
        return nullable

    while not stable:
        for n in gramm.nonterminals:
            if n not in nullable:
                for p in gramm.productions:
                    if p.lhs == n:
                        x = p.rhs
                        for xx in x:
                            if xx not in nullable:
                                loop_broke = True
                                xctr += 1
                                if xctr >= (len(gramm.nonterminals) * 2):
                                    stable = True
                                break
                        if not loop_broke:
                            bb = set([n])
                            cc = nullable.union(bb)
                            nullable = cc
                            ctr += 1
                            if ctr >= 1:
                                stable = True
                            foundE = False
                        loop_broke = False

    return nullable


def computeFirst(gramm):
    ''' Return a dict(list) of each nonterminal with its corresponding first set '''
    global start_symbol

    first = {}
    nulls = computeNullable(gramm)
    #print("NULLABLE:", nulls)
    stable = False
    udates = 0

    for t in gramm.terminals:
        first[t] = set([t])

    # Initialize NonTerminals in first set
    for tt in gramm.nonterminals:
        first[tt] = set()

    print('')

    while not stable:
        for n in gramm.nonterminals:
            for p in gramm.productions:
                if p.lhs == n:
                    for x in p.rhs:
                        if x != epsilon and x != ' ':
                            c = first[n].union(first[x])
                            first[n] = c
                            # print("first[",n,"]:", first[n])
                            udates += 1
                            if x not in nulls:
                                break
        if udates >= len(gramm.nonterminals) * len(gramm.terminals):
            stable = True

    return [first, nulls]


def computeFollow(gramm, firstSet, nullableSet):
    '''Computes and returns a set of follows for each production in the
       specified grammar. '''
    global start_symbol

    follow = {start_symbol: set(['$'])}

    # Initialize NonTerminals in follow set
    for tt in gramm.nonterminals:
        if tt != start_symbol:
            follow[tt] = set()

    stable = False
    broke_complex = False
    udates = 0

    while not stable:
        for n in gramm.nonterminals:
            for p in gramm.productions:
                if p.lhs == n:
                    for i in range(len(p.rhs)):
                        x = p.rhs[i]
                        if x in gramm.nonterminals:
                            for y in p.rhs[i + 1:]:
                                c = follow[x].union(set(firstSet[y]))
                                follow[x] = c
                                udates += 1
                                if y not in nullableSet:
                                    broke_complex = True
                                    break
                            if not broke_complex:
                                c = follow[x].union(set(follow[n]))
                                follow[x] = c
                                udates += 1
                            else:
                                broke_complex = False

        if udates >= len(gramm.nonterminals) * (len(gramm.terminals) * 2):
            stable = True

    return follow


def makeTree(I, N, iput):
    print("Item:", I)
    print("I.how:", I.how)

    if I.how == "INITIAL":
        N.sym = "S'"
        return N
    elif I.how[0] == "S": #symbol            token
        tnode = TreeNode(I.rhs[I.dpos-1], iput[I.column-1])
        print("Prepending Scan Node:", tnode)
        N.prepend_child(tnode)
        nitem = Item(I.lhs[I.dpos], I.rhs[I.dpos-1], I.dpos, ["P"], I.column)
        #return makeTree(I.how[1], N, iput)
        return makeTree(nitem, N, iput)
    elif I.how[0] == "P":
        N.sym = "Adam is not great"
        return N
    elif I.how[0] == "C":
        #Items
        completed = I.how[2] # Play with index
        partial = I.how[1] # Play with index
        print("Completed:", completed)
        print("Partial:", partial)
        Q = TreeNode(completed[0], partial[0])# completed.lhs
        print("Prepending Complete Node:", Q)
        N.prepend_child(Q)
        makeTree(completed, Q, iput)
        return makeTree(partial, N, iput)


def earleyParse(iput, gramm, SSym):
    global tokens

    # • <- a very friendly dot :)

    Ilen = len(iput)

    if Ilen <= 1:
        return [iput, False, iput[0]]

    T = {}

    for i in range(Ilen+1):
        for j in range(Ilen+1):
            if j >= i:
                T[(i, j)] = set()

    bSym = SSym
    SSym = "S'"
    Start_Node = TreeNode("S'", Token("S_PRIME", "S'", -1))

    # Add the initial Start Symbol to the parse table.
    T[(0, 0)].add((SSym, bSym, 0))

    col = 0

    for col in range(0, Ilen+1):
        flag = True
        while flag:
            flag = False
            for row in range(0, col + 1):
                if (row, col) in T:
                    for I in T[(row, col)].copy():
                        lhs = I[0]
                        rhs = I[1].split(' ')
                        dpos = I[2]

                        how = "INITIAL"
                        tadpos = ''
                        if dpos == 0:
                            tadpos = rhs[0]
                        elif dpos == len(rhs):
                            tadpos = ''
                        else:
                            tadpos = rhs[dpos]

                        if col < Ilen:
                            if iput[col].symbol == tadpos or iput[col].lexeme == tadpos:
                                # SCAN
                                how = ["S"]
                                #print("SCANNING")
                                nrhs = ""
                                for xx in rhs:
                                    nrhs += xx
                                    nrhs += ' '
                                nrhs = nrhs[:-1]

                                I2New = (lhs, nrhs, dpos + 1)
                                if I2New not in T[(row, col + 1)]:
                                    T[(row, col + 1)].add(I2New)
                                    #print("Added Scan set", I2New, "to T[", row, "][", col + 1, "]")
                                    flag = True
                                    #print("Set Flag in SCAN.\n")
                                    how.append(I2New)

                        if tadpos in gramm.nonterminals:
                            # PREDICT
                            # Add all productions with lhs of rhs[dpos] to T[col][col]
                            # Might set flag to True
                            # print("PREDICTING")
                            how = ["P"]
                            for prodd in gramm.productions:
                                nrhs = ""
                                for kl in range(len(prodd.rhs)):
                                    nrhs += prodd.rhs[kl]
                                    nrhs += ' '
                                nrhs = nrhs[:-1]

                                newThing = (prodd.lhs, nrhs, 0)
                                if prodd.lhs == rhs[dpos]:
                                    if newThing not in T[(col, col)]:
                                        T[(col, col)].add(newThing)
                                        #print("Added", newThing, "to predict set", "T[", col, "][", col, "]")
                                        flag = True
                                        #print("Set Flag in PREDICT.\n")
                                        how.append(newThing)

                        # COMPLETE
                        if tadpos == '':
                            # print("Completing?")
                            how = ["C"]
                            for k in range(0, row+1):
                                for Itwo in T[(k, row)].copy():
                                    lhs2 = Itwo[0]
                                    rhs2 = Itwo[1].split(' ')
                                    dpos2 = Itwo[2]

                                    # I2.rhs[I2.dpos]
                                    ItwoDposSide = 0
                                    if dpos2 < len(rhs2):
                                        ItwoDposSide = rhs2[dpos2]

                                    # if I.lhs matches I2.rhs[I2.dpos]:
                                    if lhs == ItwoDposSide:
                                        Nrhs2 = ""
                                        for fk in rhs2:
                                            Nrhs2 += fk
                                            Nrhs2 += ' '
                                        Nrhs2 = Nrhs2[:-1]

                                        newerthing = (lhs2, Nrhs2, dpos2 + 1)
                                        if newerthing not in T[(k, col)]:
                                            #print("COMPLETING")
                                            T[(k, col)].add(newerthing)
                                            #print("Added", newerthing, "to complete set.", "T[", row, "][", col + 1, "]")
                                            flag = True
                                            #print("Set Flag in COMPLETE.\n")
                                            how.append([lhs, rhs, dpos]) #Partial
                                            how.append(newerthing) #Complete

                        #if row == 0 and col == 0:
                        #    if lhs == "S'" and rhs == "S":
                        #        print(lhs, rhs, dpos)
                        #        how = "INITIAL"
                        #titem = Item(lhs, rhs, dpos, how, col)
                        #print("Titem:", titem)
                        #Start_Node = makeTree(titem, Start_Node, iput)
                        #print("New Node:", Start_Node)
                        #print("Node's Children amount:", len(Start_Node.children))

    cParse = False

    LCell = T[(0, Ilen)]

    #print(T[(0, 0)])

    if len(LCell) > 0:
        lastCell = []
        lCol = LCell
        while lCol:
            x = lCol.pop()
            lastCell.append(x)
        #print("LastCell:", lastCell)

        for gg in lastCell:
            if gg[0] == SSym:
                if gg[1] == bSym and gg[2] == 1:
                    cParse = True
                    return [iput, cParse, iput[col-1], T]

    return [iput, cParse, iput[col-1], T]


def createGrammar():
    textList = []

    grammy = open('grammar.txt', 'r+')
    for g in grammy:
        #print(g)
        if g == "\n":
            #print("EMPTY")
            continue
        else:
            gg = ""
            for xx in range(len(g)-1):
                gg += g[xx]
            textList.append(gg)

    termsList = []
    nontermsList = []
    productionList = []

    terms = open('terminals.txt', 'r+')

    for t in terms:
        xdf = t.split(' ')
        for xx in xdf:
            termsList.append(xx)
    terms.close()

    nts = open('nonterminals.txt', 'w')
    wroteSet = set()
    for txx in textList:
        prod = txx

        arrow = " -> "

        splitOne = prod.split(arrow)

        lhs = splitOne[0]
        rhs = splitOne[1]

        sides = rhs.split(' | ')

        for xc in range(len(sides)):
            tmp = ""
            tmp += lhs
            tmp += arrow
            tmp += sides[xc]
            if lhs not in wroteSet:
                nts.write(lhs)
                #if xc < len(sides)-1:
                nts.write(' ')
                wroteSet.add(lhs)
            productionList.append(Production(tmp))

    nts.close()

    nterms = open('nonterminals.txt', 'r+')

    for n in nterms:
        xdf = n.split(' ')
        if '' in xdf:
            xdf.remove('')
        for xx in xdf:
            nontermsList.append(xx)
    nterms.close()

    nontermsSet = set(nontermsList)
    termsSet = set(termsList)

    gramm = Grammar(textList, termsSet, nontermsSet, productionList)

    return gramm


def printGrammar(g):
    print("Grammar:", g.text, g.terminals, g.nonterminals)
    print("Productions:")
    for ppp in g.productions:
        print(ppp)


def main():
    global start_symbol

    tokes = tokenize(False, False)

    tkes = open('tokens.txt', 'w')

    for tt in tokes:
        tkes.write(str(tt)+'\n')
    tkes.close()

    asdf = createGrammar()
    #printGrammar(asdf)

    start_symbol = asdf.productions[0].lhs
    #print("Start Symbol:", start_symbol)

    #fir = computeFirst(asdf)

    #print("First set:", fir[0])
    #print('')

    # Grammar, FirstSet, NullableSet
    #fol = computeFollow(asdf, fir[0], fir[1])

    #print("Follow Set:", fol)
    #print('')

    print("Parsing!")
    prs = earleyParse(tokes, asdf, start_symbol)
    if not prs[1]:
        #print("Failed to Parse. Gave up around", prs[2])
        print("Failed to Parse.")
    else:
        print("Completed Parse!")

main()
