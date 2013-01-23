%{
/*
 * Constantin Serban-Radoi 333CA
 * Tema LFA
 * Ianuarie 2013
 */

#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <map>
#include <vector>
#include <deque>
#include <string>
#include <stack>
#include <set>

#define DBG 0

#define DBGOUT if (DBG) cerr

using namespace std;

class Tape;
class TuringMachine;

class TuringParser : public yyFlexLexer {
public:
    virtual int yylex();
};

enum Directions {
    Left = 0,
    Right = 1
};

enum Negate {
    DontNegate = false,
    Negate = true
};

typedef set<char> SymSet;

ostream& operator<<(ostream& os, const SymSet& set) {
    os << "{";
    for (SymSet::iterator i = set.begin(); i != set.end(); ++i)
        os << *i << ", ";
    os << "}";
    return os;
}

int lines = 0;                          /* Number of lines parsed */
Tape *tp;                               /* The tape of the program */
string currentName("");                 /* Current matched name */
string currentTemporaryName("");        /* Current temporary name for a TM */

bool currentMachineHasTemp = false;     /* Wether the current machine has a temporary name or not */

vector<char> alphabet;                  /* Contains symbols of the alphabet */
map<string, char> symbolsMap;           /* Contains definitions for symbols */
map<string, TuringMachine*> turingMap;  /* Contains Turing Machine definitions */
map<string, TuringMachine*> turingTemporaryMap; /* Contains association of temporary names for TM */

TuringMachine *currentTuringM = NULL;   /* Used to hold the current turring machine declaration */
TuringMachine *startTuringM = NULL;     /* First called Turing Machine in a declaration */
bool firstInBranch = false;             /* Marks the first machine in a branch */
bool currentTuringMIsNamed = false;     /* Wether the current machine has a name or not */

SymSet *currentSymSet = NULL;           /* Current symbol set (used for parsing) */
map<string, SymSet*> symSetNamesMap;    /* Contains named symbol sets */

stack<TuringMachine*> transitionsStack; /* Stack of transition machines */
bool currentTransitionSetNegated = false;   /* Wether the current transition set is negated or not */

void chainMachine(TuringMachine *tm);   /* Chains the current machine with this machine */
bool getMachineByName(const string &name, TuringMachine*& tm);  /* Gets machine from map */
bool getMachineByTempName(const string &name, TuringMachine*& tm);  /* Gets machine from map by temp name */
bool getSymbolByName(const string &name, char &symbol); /* Gets a symbol given its name */
bool getVariableId(const string &name, int& variableId);    /* Gets a variable id by name */

int currentTransitionVariableId;        /* Id given to the current transition */
stack<string> variableStack;            /* Stack of variables */
map<string, stack<int> > variableMap;   /* Maps variable names with names stack */
vector<char> variableSymbolsOnTape;     /* Symbol on tape for variables */

int variableNumber = 1;                 /* Counter for number of variables */



/* Class Holding tape information and methods */
class Tape {
public:
    Tape() : head(-1) {}
    Tape(char *config) {
        setTape(config);
    }

    /* Read initial tape configuration */
    void setTape(char *config) {
        int i = 0;
        while (config[i]) {
            if (config[i] != '>')
                tape.push_back(config[i++]);
            else {
                head = i++;
            }
        }
    }

    /* Reads the symbol that the head points to */
    char read() {
        return tape[head];
    }

    /* Write a symbol at the head position */
    void write(char symbol) {
        tape[head] = symbol;
        if (head == (int)tape.size() - 1)
            tape.push_back('#');
    }

    /* Move head right */
    void moveRight() {
        head++;
        if (head >= (int)tape.size() - 1) {
            tape.push_back('#');
        }
    }

    /* Move head left */
    void moveLeft() {
        head--;
        if (head <= 0) {
            tape.push_front('#');
            head++;
        }
    }

    /* Move head left or right */
    void move(bool direction) {
        if (direction == Left)
            moveLeft();
        else if (direction == Right)
            moveRight();
    }

    /* Returns the current tape */
    deque<char> getTape() {
        return tape;
    }

    /* Get head position */
    int getHeadPosition() {
        return head;
    }

    /* Crop # from left and right */
    void crop() {
        DBGOUT << "Tape before crop left: " << *this << endl;
        while (tape.size() > 2 && head > 1 && tape[0] == '#' && tape[1] == '#') {
            tape.pop_front();
            --head;
        }
        DBGOUT << "Tape before crop right: " << *this << endl;
        int countBack = 0;
        for (int i = (int)tape.size() - 1; i > 0; --i) {
            if (tape.size() > 2 && i > head && tape[i] == '#' && tape[i - 1] == '#')
                ++countBack;
            else
                break;
        }
        for (int i = 0; i < countBack; ++i)
            tape.pop_back();
        DBGOUT << "Tape after crop: " << *this << endl;
    }

    friend ostream& operator<< (ostream& os, const Tape &tp);
private:
    deque<char> tape;   // All tape symbols without '>'
    int head;           // The head position that points to the current element
};

ostream& operator<< (ostream& os, const Tape &tp) {
    for (unsigned int i = 0; i < tp.tape.size(); ++i) {
        if ((int)i == tp.head)
            os << '>';
        os << tp.tape[i];
    }
    return os;
}

/* Abstract class holding a Turing Machine */
class TuringMachine {
public:
    TuringMachine() : tm(NULL) {}
    virtual ~TuringMachine () {}

    void setNextMachine(TuringMachine *tm) {
        this->tm = tm;
    }

    virtual void execute() = 0;     // Pure virtual method

protected:
    TuringMachine *tm;              // Pointer to the next machine in chain
};

/* Holds a custom defined Turing Machine with default execute implementation */
class TuringMachineDefined : public TuringMachine {
public:
    TuringMachineDefined(TuringMachine *nextTM) {
        setNextMachine(nextTM);
    }

    virtual void execute() {
        if (NULL != tm)
            tm->execute();
    }
};

/* Class that manages Left and Right elementary Turing Machines */
class ElementaryMove : public TuringMachine {
public:
    ElementaryMove(bool direction, TuringMachine *nextTM)
        : direction(direction) {
        setNextMachine(nextTM);
    }

    virtual void execute() {
        tp->move(direction);
        DBGOUT << "Tape after move " << direction << "\n";
        DBGOUT << *tp << endl;

        if (NULL != tm)
            tm->execute();  // call next machine
    }
private:
    bool direction;     // Left or Right
};

/* Class that manages symbol writing */
class WriteSymbol: public TuringMachine {
public:
    WriteSymbol(char symbol, TuringMachine *nextTM)
        : symbol(symbol) {
        setNextMachine(nextTM);
    }

    virtual void execute() {
        tp->write(symbol);
        DBGOUT << "Tape after writing " << symbol << " at " << tp->getHeadPosition() << "\n";
        DBGOUT << *tp << endl;

        if (NULL != tm)
            tm->execute();  // call next machine
    }
private:
    char symbol;
};

/* Class that manages writing symbol loaded from variable */
class WriteVariable: public TuringMachine {
public:
    WriteVariable(int variableId, TuringMachine *nextTM)
        : variableId(variableId) {
        setNextMachine(nextTM);
    }

    virtual void execute() {
        tp->write(variableSymbolsOnTape[variableId]);
        DBGOUT << "Tape after writing " << variableSymbolsOnTape[variableId] << " at " << tp->getHeadPosition() << "\n";
        DBGOUT << *tp << endl;

        if (NULL != tm)
            tm->execute();  // call next machine
    }

private:
    int variableId;
};

/* Class that manages symbol reading */
class ReadSymbol: public TuringMachine {
public:
    ReadSymbol(TuringMachine *nextTM) {
        setNextMachine(nextTM);
    }

    virtual void execute() {
        symbol = tp->read();

        if (NULL != tm)
            tm->execute();  // call next machine
    }
private:
    char symbol;
};

/* Class that manages moving until a given symbol is found/not found */
class MoveUntil: public TuringMachine {
public:
    MoveUntil(bool direction, char symbol, bool negate, TuringMachine *nextTM)
        : direction(direction), symbol(symbol), negate(negate) {
        setNextMachine(nextTM);
    }

    virtual void execute() {
        bool exitWhile = false;
        do {
            tp->move(direction);
            char onTape = tp->read();
            exitWhile = (onTape == symbol) ^ negate;

            DBGOUT << "Tape after move " << direction << " until " << !negate << symbol << "\n";
            DBGOUT << *tp << endl;

        }while (!exitWhile);

        DBGOUT << "Tape after moving *until*\n";
        DBGOUT << *tp << endl;

        if (NULL != tm)
            tm->execute();  // call next machine
    }

private:
    bool direction;
    char symbol;
    bool negate;
};

/* Class that manages moving until a given symbol from variable is found/not found */
class MoveUntilVariable: public TuringMachine {
public:
    MoveUntilVariable(bool direction, int variableId, bool negate, TuringMachine *nextTM)
        : direction(direction), variableId(variableId), negate(negate) {
        setNextMachine(nextTM);
    }

    virtual void execute() {
        bool exitWhile = false;
        char symbol = variableSymbolsOnTape[variableId];
        do {
            tp->move(direction);
            char onTape = tp->read();
            exitWhile = (onTape == symbol) ^ negate;

            DBGOUT << "Tape after move " << direction << " until " << !negate << symbol << "\n";
            DBGOUT << *tp << endl;

        }while (!exitWhile);

        DBGOUT << "Tape after moving *until*\n";
        DBGOUT << *tp << endl;

        if (NULL != tm)
            tm->execute();  // call next machine
    }

private:
    bool direction;
    int variableId;
    bool negate;
};

/* Class that holds a path/branch in a transition machine. E.g: {a} -> [L] [L] */
class Transition {
public:
    Transition(TuringMachine *tm, SymSet *symbolsSet, bool negated, int variableId)
        : tm(tm), symbolsSet(symbolsSet), negated(negated), variableId(variableId) {
        DBGOUT << "Created transition on " << *symbolsSet << endl;
    }

    /* Checks if given symbol is (not) in set */
    bool checkSymbol(char symbol) {
        return symbolsSet->count(symbol) != negated;
    }

    TuringMachine* getMachine() {
        return tm;
    }
    int getVariableId() {
        return variableId;
    }
private:
    TuringMachine *tm;
    SymSet *symbolsSet;
    bool negated;
    int variableId;
};

/* Class that makes a transition based on the current symbol on tape */
class TransitionMachine : public TuringMachine {
public:
    TransitionMachine() {
        DBGOUT << "____Created Transition Machine\n";
    }

    virtual void execute() {
        char symbol = tp->read();

        DBGOUT << "Tape before transition execute: " << *tp << endl;
        DBGOUT << "will test " << transitions.size() << "for " << symbol << endl;

        /* For each transition/branch checks if the symbol matches
         * and saves it to variables array
         */
        for (unsigned int i = 0; i < transitions.size(); ++i) {
            DBGOUT << "Transition " << i << " symbol: " << symbol << endl;
            if (transitions[i].checkSymbol(symbol)) {

                int id = transitions[i].getVariableId();
                variableSymbolsOnTape[id] = symbol;

                DBGOUT << "Executing transition..." << i << " of symbol " << symbol << endl;
                transitions[i].getMachine()->execute();
                return;
            }
        }
    }

    /* Adds a new transition/branch to the current array */
    void addTransition(TuringMachine *tm, SymSet *symbolsSet, bool negated, int variableId) {
        DBGOUT << "___transition " << transitions.size() << " added for set: " << *symbolsSet << " on machine "
            << tm << " with negated = " << negated << endl;
        transitions.push_back(Transition(tm, symbolsSet, negated, variableId));
    }

public:
    vector<Transition> transitions;
};

/* Class that makes a call to a previously defined Turing Machine */
class CallMachine : public TuringMachine {
public:
    CallMachine(TuringMachine *calledTM, string name)
        : calledTM(calledTM), name(name) {
    }

    virtual void execute() {
        DBGOUT << "Executing called TM: " << name << endl;
        calledTM->execute();

        if (NULL != tm)
            tm->execute();
    }
private:
    TuringMachine *calledTM;
    string name;
};

/* Chains the current machine with tm */
void chainMachine(TuringMachine *tm) {
    DBGOUT << "DEBUG: Current name: " << currentName << " current machine " << currentTuringM << "\n";
    if (firstInBranch) {
        /* Machine is the first in its branch, e.g.: {#} -> [a] [R];
         * [a] is the first in its branch here
         */
        DBGOUT << "first in branch" << endl;

        /* Adds a the current branch to the current machine
         */
        TransitionMachine *trans = dynamic_cast<TransitionMachine*>(currentTuringM);
        trans->addTransition(tm, currentSymSet, currentTransitionSetNegated, currentTransitionVariableId);
        currentTransitionVariableId = 0;
        currentTransitionSetNegated = false;
        transitionsStack.push(currentTuringM);
        firstInBranch = false;
    }
    else {
        if (currentTuringMIsNamed) {
            // Save the current machine to the machines map
            turingMap[currentName] = tm;
            currentTuringMIsNamed = false;
        }
        else {
            currentTuringM->setNextMachine(tm);
        }
    }

    currentTuringM = tm;    // Update the current machine

    if (currentMachineHasTemp) {    // Save machine to temporary name map
        turingTemporaryMap[currentTemporaryName] = tm;
        currentMachineHasTemp = false;
    }
}

/* Gets the machine in map given its name */
bool getMachineByName(const string &name, TuringMachine*& tm) {
    map<string, TuringMachine*>::iterator it = turingMap.find(name);
    if (it == turingMap.end()) {
        cerr << "Machine " << name << " not found\n";
        return false;
    }
    tm = it->second;
    return true;
}

/* Gets the machine in map given its temporary name */
bool getMachineByTempName(const string &name, TuringMachine*& tm) {
    map<string, TuringMachine*>::iterator it = turingTemporaryMap.find(name);
    if (it == turingTemporaryMap.end()) {
        cerr << "Machine with temporary name " << name << " not found\n";
        return false;
    }
    tm = it->second;
    return true;
}

/* Gets the symbol given its name */
bool getSymbolByName(const string &name, char &symbol) {
    map<string, char>::iterator it = symbolsMap.find(name);
    if (it == symbolsMap.end()) {
        cerr << "Symbol with name " << name << " not found\n";
        return false;
    }
    symbol = it->second;
    return true;
}

/* Gets the set of symbols given its name */
bool getSymbolSetByName(const string &name, SymSet*& set) {
    map<string, SymSet*>::iterator it = symSetNamesMap.find(name);
    if (it == symSetNamesMap.end()) {
        cerr << "Symbol set with name " << name << " not found\n";
        return false;
    }
    set = it->second;
    return true;
}

/* Gets the variable id given its name */
bool getVariableId(const string &name, int& variableId) {
    map<string, stack<int> >::iterator it = variableMap.find(name);
    if (it == variableMap.end()) {
        cerr << "Variable ID for name: " << name << " not found\n";
        return false;
    }
    variableId = it->second.top();
    return true;
}

%}

%option c++
%option noyywrap
%option stack
%option yyclass="TuringParser"

/* Terminals */
LETTER          [A-Za-z]
DIGIT           [0-9]
OTHER           [#$*@]
SYMBOL          {LETTER}|{DIGIT}|{OTHER}

ALPHABET_DECL   (alphabet[ \t]*::[ \t]*)
NAME            ({LETTER}|{DIGIT}|_)*
ELEM            {SYMBOL}|<{NAME}>|&{NAME}
ELEMENTARY_LR   L|R


COMMENT         ^\;.*

/* Declarations */
SYMBOL_START    ([ \t]*{NAME}[ \t]*=[ \t]*)
SYMBOL_DECL     ([ \t]*{NAME}[ \t]*=[ \t]*{SYMBOL}[ \t]*;)
SET_DECL        ([ \t\n]*{NAME}[ \t\n]*:=[ \t\n]*{[ \t\n]{SYMBOL}[ \t\n]*(,[ \t\n]*{SYMBOL})*[ \t\n]*}[ \t\n]*;)


ELEMENTARY_CALL \[{ELEMENTARY_LR}?\(!?{ELEM}\)\]
NAME_CALL       \[{NAME}\]
MT_CALL         {NAME_CALL}|{ELEMENTARY_CALL}


/* ***** States ***** */
/* Matches alphabet declarations and saves alphabet symbols */
%s alphabetDecl
/* Wait for a name */
%s waitName
/* Matches a name and waits for =, :=, ::= or @ to go to another state*/
%s nameStart
/* Matches and saves symbol declarations. */
%s symbolDecl
/* Matches and saves symbols in a set */
%s setDecl
/* Matches and saves a Turing Machine declaration */
%s turingDecl
/* Matches a transition start */
%s transitionStart
/* Matches the -> sign of a transition branch */
%s transitionBranch


%%
\n                  { ++lines; }
{COMMENT}           { DBGOUT << "Found comment: " << yytext << endl; }
[ \t]               ;

{ALPHABET_DECL} {
    DBGOUT << "Found alphabet decl: " << yytext << endl;
    yy_push_state(alphabetDecl);
    DBGOUT << "Current state after push alph: " << yy_top_state() << endl;
}

<alphabetDecl>{
    {SYMBOL}+ {
        DBGOUT << "Found alphabet symbol: " << yytext << endl;
        alphabet.push_back(yytext[0]);
    }
    ; {
        DBGOUT << "Found alphabet END: " << yytext << endl;
        DBGOUT << "Current state: " << yy_top_state() << endl;
        yy_push_state(waitName);
        DBGOUT << "Current state: " << yy_top_state() << endl;
    }
}

<waitName>{
    {NAME} { DBGOUT << "Found name: " << yytext << endl;
        currentName = yytext;
        yy_push_state(nameStart);
        DBGOUT << "Current state: " << yy_top_state() << endl;
    }

}

<nameStart>{
    = {
        DBGOUT << "Found symbol-decl start: " << yytext << endl;
        yy_push_state(symbolDecl);
        DBGOUT << "Current state: " << yy_top_state() << endl;
    }
    :=[ \t\n]*\{ {
        DBGOUT << "Found set-decl start: " << yytext << endl;
        currentSymSet = new SymSet();
        symSetNamesMap[currentName] = currentSymSet;
        yy_push_state(setDecl);
        DBGOUT << "Current state: " << yy_top_state() << endl;
    }
    ::= {
        DBGOUT << "Found Turing-Machine start: " << yytext << endl;

        DBGOUT << "Current state: " << yy_top_state() << endl;
        currentTuringMIsNamed = true;


        turingTemporaryMap.erase(turingTemporaryMap.begin(), turingTemporaryMap.end());

        transitionsStack.push(NULL);

        yy_push_state(turingDecl);
    }
    ; {
        DBGOUT << "Found end decl: " << yytext << endl;
        DBGOUT << "Current name: " << currentName << endl;
        DBGOUT << "Current state: " << yy_top_state() << endl;
        yy_pop_state();
    }
}

<symbolDecl>{
    {SYMBOL} {
        DBGOUT << "Found declared symbol: " << yytext << endl;
        symbolsMap[currentName] = yytext[0];
        DBGOUT << "pair: (" << currentName << "," << symbolsMap[currentName] << ")" << endl;
        DBGOUT << "Current state: " << yy_top_state() << endl;
        yy_pop_state();
    }
}

<setDecl>{
    , ;
    {SYMBOL} {
        DBGOUT << "Found set_symbol: " << yytext << endl;
        currentSymSet->insert(yytext[0]);
    }
    \<{NAME}\> {
        string name = string(yytext).substr(1, yyleng - 2);
        DBGOUT << "Found set symbol with name " << name << endl;

        char symbol = 0;
        if (getSymbolByName(name, symbol)) {
            DBGOUT << "The symbol with name " << name << " is " << symbol << endl;
            currentSymSet->insert(symbol);
        }
    }
    \} {
        DBGOUT << "Found end of set decl: " << yytext << endl;
        DBGOUT << "Current state: " << yy_top_state() << endl;
        yy_pop_state();
    }
}

<turingDecl>{
    {NAME}@ {   // Optional temporary name
        currentMachineHasTemp = true;
        currentTemporaryName = string(yytext).substr(0, yyleng - 1);
        DBGOUT << "Temporary name: " << currentTemporaryName << endl;

    }
    \[[LR]\] {  // Elementary L or R
        DBGOUT << "Found " << yytext << " machine\n";
        TuringMachine *m = new ElementaryMove((yytext[1] == 'R'), NULL);

        chainMachine(m);
    }
    \[{SYMBOL}\] {  // Elementary write symbol
        DBGOUT << "Found " << yytext << " machine\n";
        TuringMachine *m = new WriteSymbol(yytext[1], NULL);

        chainMachine(m);
    }
    \[{NAME}\] {    // Call by name
        string name = string(yytext).substr(1, yyleng - 2);
        DBGOUT << "Found call by name: " << name << endl;

        TuringMachine *goToMachine = NULL;
        if (getMachineByName(name, goToMachine)) {
            TuringMachine *call = new CallMachine(goToMachine, name);
            chainMachine(call);
        }

    }
    \[[LR]\(!?{SYMBOL}\)\] {  // Elementary L/R (!) symbol
        DBGOUT << "Found " << yytext << " machine\n";
        TuringMachine *m = NULL;
        if (strlen(yytext) == 7) {  // With ! sign
            m = new MoveUntil((yytext[1] == 'R'), yytext[4], true, NULL);
        }
        else if (strlen(yytext) == 6) { // Without ! sign
            m = new MoveUntil((yytext[1] == 'R'), yytext[3], false, NULL);
        }

        chainMachine(m);
    }
    \[[LR]\(!?\<{NAME}\>\)\] {  // Elementary L/R (!) with brackets replaced by symbol
        DBGOUT << "Found " << yytext << " machine\n";
        bool direction = yytext[1] == 'R';
        bool negated = yytext[3] == '!';
        string name = string(yytext).substr(4 + negated, yyleng - 7 - negated);

        DBGOUT << "Extracted name " << name << endl;

        char symbol = 0;
        if (getSymbolByName(name, symbol)) {
            DBGOUT << "Symbol with name " << name << " is " << symbol << endl;
            TuringMachine *m = new MoveUntil(direction, symbol, negated, NULL);
            chainMachine(m);
        }
    }
    \[[LR]\(!?&{NAME}\)\] { // L/R (!) with a variable to a transition
        DBGOUT << "Found " << yytext << " machine\n";
        bool direction = yytext[1] == 'R';
        bool negated = yytext[3] == '!';
        string name = string(yytext).substr(4 + negated, yyleng - 6 - negated);

        DBGOUT << "Extracted name " << name << endl;
        int id = 0;
        if (getVariableId(name, id)) {
            DBGOUT << "Variable id for " << name << " = " << id << endl;

            TuringMachine *m = new MoveUntilVariable(direction, id, negated, NULL);
            chainMachine(m);
        }
    }
    \[\<{NAME}\>\] {    // Bracket call. Replaces brackets with defined symbol
        DBGOUT << "Found " << yytext << " machine\n";
        string name = string(yytext).substr(2, yyleng - 4);
        DBGOUT << "Cropped name: " << name << endl;

        char symbol = 0;
        if (getSymbolByName(name, symbol)) {
            DBGOUT << "Symbol with name " << name << " is " << symbol << endl;
            TuringMachine *m = new WriteSymbol(symbol, NULL);
            chainMachine(m);
        }
    }
    \[&{NAME}\] {   // Call variable from transition
        DBGOUT << "Found " << yytext << " machine\n";
        string name = string(yytext).substr(2, yyleng - 3);
        DBGOUT << "Cropped name: " << name << endl;

        int id = 0;
        if (getVariableId(name, id)) {
            DBGOUT << "Variable id for " << name << " = " << id << endl;

            TuringMachine *m = new WriteVariable(id, NULL);
            chainMachine(m);
        }
    }
    &{NAME} {   // Call by temporary name
        string name = string(yytext).substr(1, yyleng - 1);
        DBGOUT << "Found call by temporary name: " << name << endl;

        TuringMachine *goToMachine = NULL;
        if (getMachineByTempName(name, goToMachine))
            currentTuringM->setNextMachine(goToMachine);
    }

    \( {    // Found a transition start
        DBGOUT << "Found beginning of transition: " << yytext << endl;
        TuringMachine *m = new TransitionMachine();
        chainMachine(m);


        yy_push_state(transitionStart);
        DBGOUT << "Current state: " << yy_top_state() << endl;
    }

    ; {
        DBGOUT << "Found Turing-Machine declaration END: " << yytext << endl;


        yy_pop_state();
        DBGOUT << "Current state: " << yy_top_state() << endl;

        currentTuringM = transitionsStack.top();
        transitionsStack.pop();
        DBGOUT << "pop trans stack" << endl;

        if (YY_START == transitionStart) {
            /* The current state comes from a transition, so I clean up variable stack */
            TransitionMachine *transMachine = dynamic_cast<TransitionMachine*>(currentTuringM);

            vector<Transition> trans = transMachine->transitions;
            int size = trans.size();
            int variableId = trans[size - 1].getVariableId();

            if (variableId > 0) {
                variableMap[variableStack.top()].pop();
                variableStack.pop();
            }
        }
    }
}

<transitionStart>{
    {NAME}@ {   // Name for a transition to save to a variable
        string name = string(yytext).substr(0, yyleng - 1);
        DBGOUT << "Found transition name : " << name << endl;

        stack<int> &stack = variableMap[name];
        int newId = variableNumber++;
        stack.push(newId);
        variableStack.push(name);

        currentTransitionVariableId = newId;
        DBGOUT << "Current variable id is: " << newId << endl;
    }
    ! { // Transition set is negated
        DBGOUT << "Current transition set is negated\n";
        currentTransitionSetNegated = true;
    }
    \<{NAME}\> {    // Name for a full set previously defined
        string name = string(yytext).substr(1, yyleng - 2);
        DBGOUT << "Found set symbol with name " << name << endl;

        SymSet *set = NULL;
        if (getSymbolSetByName(name, set)) {
            DBGOUT << "The set with name " << name << " is " << *set << endl;
            currentSymSet = set;

            yy_push_state(transitionBranch);
        }
    }
    \{ {    // Found symbol set start
        DBGOUT << "Found new symbol set start " << yytext << endl;
        currentSymSet = new SymSet();

        yy_push_state(transitionBranch);
        yy_push_state(setDecl);
    }

    \) { // End of transition
        DBGOUT << "Found end of transition: " << yytext << endl;

        yy_pop_state();
        DBGOUT << "Current state: " << yy_top_state() << endl;
    }
}

<transitionBranch>{
    -\> {   // Found "->" sign
        DBGOUT << "Found -> sign " << yytext << endl;
        yy_pop_state();
        yy_push_state(turingDecl);
        firstInBranch = true;
    }
}

%%

int main(int argc, char *argv[]) {

    if (argc != 4) {
        cerr << "usage: " << argv[0] << " [fileName] [turingMachine] [config]\n";
        exit(EXIT_FAILURE);
    }

    ifstream file(argv[1]);
    if (!file.good()) {
        cerr << "Could not open file \n";
        exit(EXIT_FAILURE);
    }


    tp = new Tape(argv[3]);   // Init tape

    DBGOUT << *tp << "\n";

    TuringParser *TuringP = new TuringParser();

    TuringP->switch_streams(&file);

    while(TuringP->yylex() != 0);

    DBGOUT << "Total number of lines: " << lines << "\n";

    file.close();

    DBGOUT << "Alphabet: \n";
    for (unsigned int i = 0; i < alphabet.size(); ++i)
        DBGOUT << alphabet[i] << " ";
    DBGOUT << "\n";
    DBGOUT << "Symbol declarations:\n";
    for (map<string, char>::const_iterator it = symbolsMap.begin(); it != symbolsMap.end(); ++it) {
        DBGOUT << "(" << it->first << "," << it->second << ") ";
    }
    DBGOUT << "\n";
    DBGOUT << "Set declarations:\n";
    for (map<string, SymSet*>::const_iterator it = symSetNamesMap.begin(); it != symSetNamesMap.end(); ++it) {
        DBGOUT << *(it->second) << endl;
    }

    DBGOUT << "The real test:\n\n";
    DBGOUT << "Tape before: \n" << *tp << endl;

    variableSymbolsOnTape = vector<char>(variableNumber, 0);

    TuringMachine *machine = NULL;
    if (getMachineByName(argv[2], machine))
        machine->execute();

    tp->crop();

    cout << *tp << endl;

    delete TuringP;
    return 0;
}
