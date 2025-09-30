from typing import Union
class Symbol:
    def __init__(self,s:str) -> None:
        self.string = s
    def __repr__(self) -> str:
        return self.string
ε = Symbol('ε')
conc = Symbol('conc')
star = Symbol('star')
union = Symbol("union")
class State:
    id = 1
    def __init__(self):
        self.ID = State.id
        State.id += 1
    def __eq__(self, other):
        return isinstance(other, State) and self.ID == other.ID
    def __hash__(self):
        return hash(self.ID)
    def __repr__(self):
        return f"q{self.ID}"
    def __iter__(self):
        yield self
class FiniteAutomata:
    id = 1
    def __init__(self,Q:set, Σ:set[str], δ:dict[tuple[State, Union[str,Symbol]], Union[set,State]],q:State, F:set[State]):
        self.Q = self.states = Q
        self.Σ = self.alphabet =  Σ
        self.δ = self.transition_function = δ
        self.q = self.start_state = q 
        self.F = self.final_states = F
        self.ID = FiniteAutomata.id
        FiniteAutomata.id += 1
    def __repr__(self):
        return f"M{self.ID}=(Q={self.Q},\nΣ={self.Σ},\nδ={self.δ},\nq={self.q},\nF={self.F})"
    def E(self,R:Union[set[State], State]) -> set[State]:
        if R is None:return set()
        if isinstance(R,set):
            closure = set(R)
            stack = list(R)
        else:
            closure = {R}
            stack = [R]
        while stack:
            state = stack.pop()
            S = self.δ.get((state,ε))
            if S is None:continue
            if isinstance(S,set):
                for next in S:
                    if next not in closure:
                        closure.add(next)
                        stack.append(next)
            else:
                if S not in closure:
                    closure.add(S)
                    stack.append(S)
        return closure
    def computation(self,w:str) -> bool:
        r:set = self.E(set([self.q]))
        for i in w:
            r1 = set()
            for q in r:
                r1 = r1.union(self.E(self.δ.get((q,i))))
            r = r1
            print(f"({i}, {r})")
        for q in r:
            if q in self.F:
                print(f'M{self.ID} accepts {w}')
                return True
        print(f'M{self.ID} rejects {w}')
        return False 
    def determinization(self) -> "FiniteAutomata":
        NFAstart = self.E(self.q)
        stack = [NFAstart]
        NFA_state_to_DFA = {frozenset(NFAstart):State()}
        q = NFA_state_to_DFA[frozenset(NFAstart)]
        δ:dict[tuple[State, Union[str,Symbol]], State] = dict()
        F = set()
        while stack:
            NFAstate = stack.pop()
            DFAstate = NFA_state_to_DFA[frozenset(NFAstate)]
            if any(q in self.F for q in NFAstate):
                F.add(DFAstate)
            for s in self.Σ:
                new = set()
                for NFAq in NFAstate:
                    new = new.union(self.E(self.δ.get((NFAq,s))))
                newfrozen = frozenset(new)
                if newfrozen not in NFA_state_to_DFA:
                    NFA_state_to_DFA[newfrozen] = State()
                    stack.append(new)
                δ[(DFAstate, s)] = NFA_state_to_DFA[newfrozen]
        Q = set(NFA_state_to_DFA.values())
        Σ = self.Σ
        return FiniteAutomata(Q,Σ,δ,q,F)
    @staticmethod
    def union(M1:"FiniteAutomata", M2:"FiniteAutomata") -> "FiniteAutomata":
        q0 = State()
        Q = {q0}|M1.Q|M2.Q
        Σ = M1.Σ|M2.Σ
        F = M1.F|M2.F
        δ = dict()
        for transition in M1.δ:
            δ[transition] = M1.δ[transition]
        for transition in M2.δ:
            if transition in δ:δ[transition] = set(δ[transition])|set(M2.δ[transition])
            else:δ[transition] = M2.δ[transition]
        δ[(q0,ε)] = {M1.q,M2.q}
        return FiniteAutomata(Q,Σ,δ,q0,F)    
    @staticmethod
    def concatenation(M1:"FiniteAutomata", M2:"FiniteAutomata") -> "FiniteAutomata":
        Q = M1.Q|M2.Q
        Σ = M1.Σ|M2.Σ
        q = M1.q
        F = set(M2.F)
        δ = dict()
        for transition in M1.δ:
            if (transition[0] in M1.Q - M1.F) or (transition[0] in M1.F and transition[1] != ε):
                δ[transition] = M1.δ[transition]
            elif transition[0] in M1.F and transition[1] == ε:
                δ[transition] = set(M1.δ[transition])|{M2.q}
        for state in M1.F:
            if (state,ε) not in δ:
                δ[(state,ε)] = M2.q
        for transition in M2.δ:
            δ[transition] = M2.δ[transition]
        return FiniteAutomata(Q,Σ,δ,q,F)
    @staticmethod
    def star(M:"FiniteAutomata"):
        q = State()
        Q = M.Q|{q}
        F = M.F|{q}
        δ = dict()
        for transition in M.δ:
            if (transition[0] in M.Q - M.F) or (transition[0] in M.F and transition[1] != ε):
                δ[transition] = M.δ[transition]
            elif transition[0] in M.F and transition[1] == ε:
                δ[transition] = set(M.δ[transition])|{M.q}
        for state in M.F:
            if (state,ε) not in δ:
                δ[(state,ε)] = M.q
        δ[(q,ε)] = M.q
        return FiniteAutomata(Q,M.Σ,δ,q,F)
class RegularLanguages:
    @staticmethod
    def parse(txt: str) -> Union[list, str]:
        if not txt:
            return 'ε'
        class Parser:
            def __init__(self, s: str):
                self.s = s
                self.n = len(s)
                self.i = 0

            def peek(self):
                return self.s[self.i] if self.i < self.n else None

            def eat(self, ch=None):
                if self.i < self.n:
                    c = self.s[self.i]
                    if ch and c != ch:
                        raise Exception(f"Expected '{ch}' at {self.i}, got '{c}'")
                    self.i += 1
                    return c
                return None

            def parse_union(self):
                node = self.parse_concat()
                while self.peek() == "|":
                    self.eat("|")
                    rhs = self.parse_concat()
                    node = [union, node, rhs]
                return node

            def parse_concat(self):
                nodes = []
                while self.peek() and self.peek() not in ")|":
                    nodes.append(self.parse_star())
                if not nodes:
                    return 'ε'
                node = nodes[0]
                for nxt in nodes[1:]:
                    node = [conc, node, nxt]
                return node

            def parse_star(self):
                node = self.parse_atom()
                while self.peek() == "*":
                    self.eat("*")
                    node = [star, node]
                return node

            def parse_atom(self):
                c = self.peek()
                if c is None:
                    return 'ε'
                if c == "(":
                    self.eat("(")
                    node = self.parse_union()
                    if self.peek() != ")":
                        raise Exception("Unmatched parenthesis")
                    self.eat(")")
                    return node
                else:
                    self.eat()
                    return c

        parser = Parser(txt)
        node = parser.parse_union()
        if parser.peek() is not None:
            raise Exception(f"Unexpected input at {parser.i}: '{parser.peek()}'")
        return node
    @staticmethod
    def regexToNFA(parse_tree) -> FiniteAutomata:
        if isinstance(parse_tree,str):
            if parse_tree == 'ε':
                q = State()
                M = FiniteAutomata({q},set(),dict(),q,{q})
                return M
            q1 = State()
            q2 = State()
            Q = {q1,q2}
            Σ = {parse_tree}
            δ = {(q1,parse_tree):q2}
            F = {q2}
            M = FiniteAutomata(Q,Σ,δ,q1,F)
        else:
            if parse_tree[0] == conc:M = FiniteAutomata.concatenation(RegularLanguages.regexToNFA(parse_tree[1]),RegularLanguages.regexToNFA(parse_tree[2]))
            elif parse_tree[0] == star:M = FiniteAutomata.star(RegularLanguages.regexToNFA(parse_tree[1]))
            elif parse_tree[0] == union:M = FiniteAutomata.union(RegularLanguages.regexToNFA(parse_tree[1]),RegularLanguages.regexToNFA(parse_tree[2]))
        return M

class MultiInputFiniteAutomata:
    id = 1
    def __init__(self,Q:set, Σ:set[tuple[str]], δ:dict[tuple[State, tuple[Union[str,Symbol]]], Union[set,State]],q:State, F:set[State], n:int) -> None:    
        self.Q = self.states = Q
        self.Σ = self.alphabet =  Σ
        self.δ = self.transition_function = δ
        self.q = self.start_state = q 
        self.F = self.final_states = F
        self.n = self.input_strings_number = n
        self.ID = FiniteAutomata.id
        FiniteAutomata.id += 1
    def __repr__(self):
        return f"M{self.ID}=(Q={self.Q},\nΣ={self.Σ},\nδ={self.δ},\nq={self.q},\nF={self.F},\nn={self.n})"
    def E(self,R:Union[set[State], State]) -> set[State]:
        if R is None:return set()
        if isinstance(R,set):
            closure = set(R)
            stack = list(R)
        else:
            closure = {R}
            stack = [R]
        while stack:
            state = stack.pop()
            S = self.δ.get((state,ε))
            if S is None:continue
            if isinstance(S,set):
                for next in S:
                    if next not in closure:
                        closure.add(next)
                        stack.append(next)
            else:
                if S not in closure:
                    closure.add(S)
                    stack.append(S)
        return closure
    def computation(self,*w:str) -> bool:
        if len(w) != self.n:raise Exception("The number of inputs doesn't equal to the specified number of inputs!")
        if any(len(w[i]) != len(w[i+1]) for i in range(len(w)-1)):raise Exception("Input strings must have the same length!")
        r:set = self.E({self.q})
        for i in range(len(w[0])):
            t = tuple(s[i] for s in w)
            r1 = set()
            for q in r:
                r1 = r1.union(self.E(self.δ.get((q,t))))
            r = r1
            print(f"({t},{r})")
        for q in r:
            if q in self.F:
                print(f'M{self.ID} accepts {w}')
                return True
        print(f'M{self.ID} rejects {w}')
        return False
    def determinization(self) -> "MultiInputFiniteAutomata":
        NFAstart = self.E(self.q)
        stack = [NFAstart]
        NFA_state_to_DFA = {frozenset(NFAstart):State()}
        q = NFA_state_to_DFA[frozenset(NFAstart)]
        δ:dict[tuple[State, tuple[Union[str,Symbol]]], State] = dict()
        F = set()
        while stack:
            NFAstate = stack.pop()
            DFAstate = NFA_state_to_DFA[frozenset(NFAstate)]
            if any(q in self.F for q in NFAstate):
                F.add(DFAstate)
            for s in self.Σ:
                new = set()
                for NFAq in NFAstate:
                    new = new.union(self.E(self.δ.get((NFAq,s))))
                newfrozen = frozenset(new)
                if newfrozen not in NFA_state_to_DFA:
                    NFA_state_to_DFA[newfrozen] = State()
                    stack.append(new)
                δ[(DFAstate, s)] = NFA_state_to_DFA[newfrozen]
        Q = set(NFA_state_to_DFA.values())
        Σ = self.Σ
        return MultiInputFiniteAutomata(Q,Σ,δ,q,F,self.n)

class FiniteStateTransducer:
    id = 1
    def __init__(self,Q:set, Σ:set[str], δ:dict[tuple[State, str], tuple[State, str]],q:State, Γ:set[str]) -> None:
        if len(δ) != len(Q)*len(Σ):raise Exception("A finite state transducer must be deterministic!")
        if any(t[1] == ε for t in δ):raise Exception("A finite state transducer must be deterministic!")
        self.Q = self.states = Q
        self.Σ = self.input_alphabet =  Σ
        self.δ = self.transition_function = δ
        self.q = self.start_state = q 
        self.Γ = self.output_alphabet = Γ
        self.ID = FiniteAutomata.id
        FiniteAutomata.id += 1
    def __repr__(self):
        return f"M{self.ID}=(Q={self.Q},\nΣ={self.Σ},\nδ={self.δ},\nq={self.q},\nΓ={self.Γ})" 
    def computation(self,w:str):
        q = self.q
        output_string = ''
        for s in w:
            if (q,s) not in self.δ:raise Exception(f"No transition defined for ({q},{s})!")
            q,o = self.δ[(q,s)]
            output_string+=o
            print(f"{s}, {q}, {output_string}")
        return output_string
    
class MultiInputFiniteStateTransducer:
    id = 1
    def __init__(self,Q:set, Σ:set[tuple[str]], δ:dict[tuple[State, tuple[str]], tuple[State, str]],q:State, Γ:set[str], n:int) -> None:
        if len(δ) != len(Q)*len(Σ):raise Exception("A finite state transducer must be deterministic!")
        if any(t[1] == ε for t in δ):raise Exception("A finite state transducer must be deterministic!")
        self.Q = self.states = Q
        self.Σ = self.input_alphabet =  Σ
        self.δ = self.transition_function = δ
        self.q = self.start_state = q 
        self.Γ = self.output_alphabet = Γ
        self.n = self.input_strings_number = n
        self.ID = FiniteAutomata.id
        FiniteAutomata.id += 1
    def __repr__(self):
        return f"M{self.ID}=(Q={self.Q},\nΣ={self.Σ},\nδ={self.δ},\nq={self.q},\nΓ={self.Γ}\nn={self.n})" 
    def computation(self,*w:str):
        if len(w) != self.n:raise Exception("The number of inputs doesn't equal to the specified number of inputs!")
        if any(len(w[i]) != len(w[i+1]) for i in range(len(w)-1)):raise Exception("Input strings must have the same length!")
        q = self.q
        output_string = ''
        for i in range(len(w[0])):
            t = tuple(s[i] for s in w)
            if (q,t) not in self.δ:raise Exception(f"No transition defined for ({q},{t})!")
            q,o = self.δ[(q,t)]
            output_string+=o
            print(f"{t}, {q}, {output_string}")
        return output_string
    
