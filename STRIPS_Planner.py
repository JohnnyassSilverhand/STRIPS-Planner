
import re
import itertools
from copy import deepcopy
import time
import queue
import sys

class Action:

    #-----------------------------------------------
    # Initialize
    #-----------------------------------------------

    def __init__(self, name, parameters, positive_preconditions, negative_preconditions, add_effects, del_effects, extensions = None):
        def frozenset_of_tuples(data):
            return frozenset([tuple(t) for t in data])
        self.name = name
        self.parameters = parameters
        self.positive_preconditions = frozenset_of_tuples(positive_preconditions)
        self.negative_preconditions = frozenset_of_tuples(negative_preconditions)
        self.add_effects = frozenset_of_tuples(add_effects)
        self.del_effects = frozenset_of_tuples(del_effects)

    #-----------------------------------------------
    # to String
    #-----------------------------------------------

    def __str__(self):
        return 'action: ' + self.name + \
        '\n  parameters: ' + str(self.parameters) + \
        '\n  positive_preconditions: ' + str([list(i) for i in self.positive_preconditions]) + \
        '\n  negative_preconditions: ' + str([list(i) for i in self.negative_preconditions]) + \
        '\n  add_effects: ' + str([list(i) for i in self.add_effects]) + \
        '\n  del_effects: ' + str([list(i) for i in self.del_effects]) + '\n'

    #-----------------------------------------------
    # Equality
    #-----------------------------------------------

    def __eq__(self, other):
        return self.__dict__ == other.__dict__

    #-----------------------------------------------
    # Groundify
    #-----------------------------------------------

    def groundify(self, objects, types):
        if not self.parameters:
            yield self
            return
        type_map = []
        variables = []
        for var, type in self.parameters:
            type_stack = [type]
            items = []
            while type_stack:
                t = type_stack.pop()
                if t in objects:
                    items += objects[t]
                if t in types:
                    type_stack += types[t]
            type_map.append(items)
            variables.append(var)
        for assignment in itertools.product(*type_map):
            positive_preconditions = self.replace(self.positive_preconditions, variables, assignment)
            negative_preconditions = self.replace(self.negative_preconditions, variables, assignment)
            add_effects = self.replace(self.add_effects, variables, assignment)
            del_effects = self.replace(self.del_effects, variables, assignment)
            yield Action(self.name, assignment, positive_preconditions, negative_preconditions, add_effects, del_effects)

    #-----------------------------------------------
    # Replace
    #-----------------------------------------------

    def replace(self, group, variables, assignment):
        new_group = []
        for pred in group:
            pred = list(pred)
            for i, p in enumerate(pred):
                if p in variables:
                    pred[i] = assignment[variables.index(p)]
            new_group.append(pred)
        return new_group


class PDDL_Parser:

    SUPPORTED_REQUIREMENTS = [':strips', ':negative-preconditions', ':typing']

    #-----------------------------------------------
    # Tokens
    #-----------------------------------------------

    def scan_tokens(self, filename):
        with open(filename) as f:
            # Remove single line comments
            str = re.sub(r';.*$', '', f.read(), flags=re.MULTILINE).lower()
        # Tokenize
        stack = []
        list = []
        for t in re.findall(r'[()]|[^\s()]+', str):
            if t == '(':
                stack.append(list)
                list = []
            elif t == ')':
                if stack:
                    l = list
                    list = stack.pop()
                    list.append(l)
                else:
                    raise Exception('Missing open parentheses')
            else:
                list.append(t)
        if stack:
            raise Exception('Missing close parentheses')
        if len(list) != 1:
            raise Exception('Malformed expression')
        return list[0]

    #-----------------------------------------------
    # Parse domain
    #-----------------------------------------------

    def parse_domain(self, domain_filename):
        tokens = self.scan_tokens(domain_filename)
        if type(tokens) is list and tokens.pop(0) == 'define':
            self.domain_name = 'unknown'
            self.requirements = []
            self.types = {}
            self.objects = {}
            self.actions = []
            self.predicates = {}
            while tokens:
                group = tokens.pop(0)
                t = group.pop(0)
                if t == 'domain':
                    self.domain_name = group[0]
                elif t == ':requirements':
                    for req in group:
                        if not req in self.SUPPORTED_REQUIREMENTS:
                            raise Exception('Requirement ' + req + ' not supported')
                    self.requirements = group
                elif t == ':constants':
                    self.parse_objects(group, t)
                elif t == ':predicates':
                    self.parse_predicates(group)
                elif t == ':types':
                    self.parse_types(group)
                elif t == ':action':
                    self.parse_action(group)
                else: self.parse_domain_extended(t, group)
        else:
            raise Exception('File ' + domain_filename + ' does not match domain pattern')

    def parse_domain_extended(self, t, group):
        print(str(t) + ' is not recognized in domain')

    #-----------------------------------------------
    # Parse hierarchy
    #-----------------------------------------------

    def parse_hierarchy(self, group, structure, name, redefine):
        list = []
        while group:
            if redefine and group[0] in structure:
                raise Exception('Redefined supertype of ' + group[0])
            elif group[0] == '-':
                if not list:
                    raise Exception('Unexpected hyphen in ' + name)
                group.pop(0)
                type = group.pop(0)
                if not type in structure:
                    structure[type] = []
                structure[type] += list
                list = []
            else:
                list.append(group.pop(0))
        if list:
            if not 'object' in structure:
                structure['object'] = []
            structure['object'] += list

    #-----------------------------------------------
    # Parse objects
    #-----------------------------------------------

    def parse_objects(self, group, name):
        self.parse_hierarchy(group, self.objects, name, False)

    # -----------------------------------------------
    # Parse types
    # -----------------------------------------------

    def parse_types(self, group):
        self.parse_hierarchy(group, self.types, 'types', True)

    #-----------------------------------------------
    # Parse predicates
    #-----------------------------------------------

    def parse_predicates(self, group):
        for pred in group:
            predicate_name = pred.pop(0)
            if predicate_name in self.predicates:
                raise Exception('Predicate ' + predicate_name + ' redefined')
            arguments = {}
            untyped_variables = []
            while pred:
                t = pred.pop(0)
                if t == '-':
                    if not untyped_variables:
                        raise Exception('Unexpected hyphen in predicates')
                    type = pred.pop(0)
                    while untyped_variables:
                        arguments[untyped_variables.pop(0)] = type
                else:
                    untyped_variables.append(t)
            while untyped_variables:
                arguments[untyped_variables.pop(0)] = 'object'
            self.predicates[predicate_name] = arguments

    #-----------------------------------------------
    # Parse action
    #-----------------------------------------------

    def parse_action(self, group):
        name = group.pop(0)
        if not type(name) is str:
            raise Exception('Action without name definition')
        for act in self.actions:
            if act.name == name:
                raise Exception('Action ' + name + ' redefined')
        parameters = []
        positive_preconditions = []
        negative_preconditions = []
        add_effects = []
        del_effects = []
        extensions = None
        while group:
            t = group.pop(0)
            if t == ':parameters':
                if not type(group) is list:
                    raise Exception('Error with ' + name + ' parameters')
                parameters = []
                untyped_parameters = []
                p = group.pop(0)
                while p:
                    t = p.pop(0)
                    if t == '-':
                        if not untyped_parameters:
                            raise Exception('Unexpected hyphen in ' + name + ' parameters')
                        ptype = p.pop(0)
                        while untyped_parameters:
                            parameters.append([untyped_parameters.pop(0), ptype])
                    else:
                        untyped_parameters.append(t)
                while untyped_parameters:
                    parameters.append([untyped_parameters.pop(0), 'object'])
            elif t == ':precondition':
                self.split_predicates(group.pop(0), positive_preconditions, negative_preconditions, name, ' preconditions')
            elif t == ':effect':
                self.split_predicates(group.pop(0), add_effects, del_effects, name, ' effects')
            else: extensions = self.parse_action_extended(t, group)
        self.actions.append(Action(name, parameters, positive_preconditions, negative_preconditions, add_effects, del_effects, extensions))

    def parse_action_extended(self, t, group):
        print(str(t) + ' is not recognized in action')

    #-----------------------------------------------
    # Parse problem
    #-----------------------------------------------

    def parse_problem(self, problem_filename):
        def frozenset_of_tuples(data):
            return frozenset([tuple(t) for t in data])
        tokens = self.scan_tokens(problem_filename)
        if type(tokens) is list and tokens.pop(0) == 'define':
            self.problem_name = 'unknown'
            self.state = frozenset()
            self.positive_goals = frozenset()
            self.negative_goals = frozenset()
            while tokens:
                group = tokens.pop(0)
                t = group.pop(0)
                if t == 'problem':
                    self.problem_name = group[0]
                elif t == ':domain':
                    if self.domain_name != group[0]:
                        raise Exception('Different domain specified in problem file')
                elif t == ':requirements':
                    pass # Ignore requirements in problem, parse them in the domain
                elif t == ':objects':
                    self.parse_objects(group, t)
                elif t == ':init':
                    self.state = frozenset_of_tuples(group)
                elif t == ':goal':
                    positive_goals = []
                    negative_goals = []
                    self.split_predicates(group[0], positive_goals, negative_goals, '', 'goals')
                    self.positive_goals = frozenset_of_tuples(positive_goals)
                    self.negative_goals = frozenset_of_tuples(negative_goals)
                else: self.parse_problem_extended(t, group)
        else:
            raise Exception('File ' + problem_filename + ' does not match problem pattern')

    def parse_problem_extended(self, t, group):
        print(str(t) + ' is not recognized in problem')

    #-----------------------------------------------
    # Split predicates
    #-----------------------------------------------

    def split_predicates(self, group, positive, negative, name, part):
        if not type(group) is list:
            raise Exception('Error with ' + name + part)
        if group[0] == 'and':
            group.pop(0)
        else:
            group = [group]
        for predicate in group:
            if predicate[0] == 'not':
                if len(predicate) != 2:
                    raise Exception('Unexpected not in ' + name + part)
                negative.append(predicate[-1])
            else:
                positive.append(predicate)

#-----------------------------------------------
# Initialize, print the parsed domain and problem 
#-----------------------------------------------
def initial(domain, problem):
    parser = PDDL_Parser()
    parser.parse_domain(domain)
    parser.parse_problem(problem)
    print('Domain name: ' + parser.domain_name)
    action = {}
    for act in parser.actions:
        #print(act)
        action.update({act.name: {  
                                    'name': act.name,
                                    'para': act.parameters,
                                    'pos_pre':[list(i) for i in act.positive_preconditions],
                                    'neg_pre':[list(i) for i in act.negative_preconditions],
                                    'add_effe':[list(i) for i in act.add_effects],
                                    'del_effe':[list(i) for i in act.del_effects]}})
    #print('----------------------------')
    print('Problem name: ' + parser.problem_name)
    #print('Objects: ' + str(parser.objects))
    #print('State: ' + str([list(i) for i in parser.state]))
    #print('Positive goals: ' + str([list(i) for i in parser.positive_goals]))
    #print('Negative goals: ' + str([list(i) for i in parser.negative_goals]))
    prob = {}
    prob.update({   'obj':parser.objects,
                    'state':[list(i) for i in parser.state],
                    'pos_goal':[list(i) for i in parser.positive_goals],
                    'neg_goal':[list(i) for i in parser.negative_goals]})
    return action,prob
    
    

    
class STRIPS_Planner:
    def __init__(self, action, prob):
        """Initialize the class

        Args:
            action (dict): the actions in domain file parsed by PDDL_Parser
            prob (dict): the problem information in problem file parsed by PDDL_Parser
        
        该类含有五个类成员变量:
        action: domain文件中的action
        state: prob字典中的state值,即初始状态
        pos: prob字典中的pos_goal值,即目标肯定状态
        neg: prob字典中的neg_goal值,即目标否定状态
        obj: prob字典中的obj值,即该问题中存在的对象
        """
        self.action = action
        self.state = [tuple(i) for i in prob['state']]
        self.pos = [tuple(i) for i in prob['pos_goal']]
        self.neg = [tuple(i) for i in prob['neg_goal']]
        self.obj = prob['obj']
        
    def get_heur(self,cur_state):
        """Evaluate the heuristic score

        Args:
            cur_state (list): a list containing atoms(tuple) to describe the current state

        Returns:
            num: the heuristic score
        """
        val = 0
        '''for i in self.pos:
            if i in cur_state:
                val -= 1
        for i in self.neg:
            if i in cur_state:
                val += 1'''
        for i in self.pos:
            if i not in cur_state:
                val += 1
        for i in self.neg:
            if i in cur_state:
                val += 1
        return val
    
    def assign(self,act):
        """Get all combinations of objects-to-parameters

        Args:
            act (dict): current chosen action

        Returns:
            list: contains all combinations of objects-to-parameters
        """
        obj = {i:{} for i in self.obj}
        for param in act['para']:
            obj[param[1]].update({param[0]:None})
        lists = [(self.obj[type], len(obj[type])) for type in self.obj]
        middle_list = [itertools.permutations(list_, num) for list_, num in lists]
        arranged = [i for i in itertools.product(*middle_list)]
        combination = []
        for arg in arranged:
            obj_temp = {i:None for type in obj for i in obj[type]}
            arg =list(itertools.chain(*arg))
            i = 0
            for type in obj_temp:
                obj_temp[type] = arg[i]
                i+=1
            combination.append(obj_temp)
        return combination
    
    def NewState(self,act,comb,cur_state):
        """Get the new state after taking the current chosen action

        Args:
            act (dict): current chosen action
            comb (dict): current chosen objects to be operated the action
            cur_state (list): current state

        Returns:
            list: new state
        """
        new = deepcopy(cur_state)
        for add in act['add_effe']:
            new.append(tuple([add[0]]+[comb[i] for i in add[1:]]))
        for sub in act['del_effe']:
            t = tuple([sub[0]]+[comb[i] for i in sub[1:]])
            if t in new:
                new.remove(t)
        return new
    
    def filter(self,act,combination,cur_state,path):
        """Choose the combinations that satisfy the preconditions of the action

        Args:
            act (dict): current chosen action
            combination (list): contains all the combinations computed by assign()
            cur_state (list): current state
            path (list): stores the current path

        Returns:
            list: If the current combination could satisfy the preconditions of the action, 
                    add a tuple shaped like (h+g,-g,new_state,new_path) as a new node to the list
        """
        filted = []
        for comb in combination:
            ToDelete = 0
            for p in act['pos_pre']:
                if tuple([p[0]]+[comb[i] for i in p[1:]]) not in cur_state:
                    ToDelete = 1
                    break
            for n in act['neg_pre']:
                if ToDelete == 1:
                    break
                elif tuple([n[0]]+[comb[i] for i in n[1:]]) in cur_state:
                    ToDelete = 1
                    break
            if ToDelete == 0:
                new_state = self.NewState(act,comb,cur_state)
                new_path = deepcopy(path)
                new_path.append([act['name'],comb])
                filted.append((self.get_heur(new_state)+len(new_path),-len(new_path),new_state,new_path))
        return filted
    
    def get_neigh(self,path,cur_state):
        """Get the neighbour nodes

        Args:
            path (list): stores the current path
            cur_state (list): current state

        Returns:
            list: a list sorted by each node's heuristic score in ascending order
        """
        neigh = []
        for act in self.action:
            comb = self.assign(self.action[act])
            neigh += self.filter(self.action[act],comb,cur_state,path)
        return sorted(neigh,key=lambda x:[x[0],x[1]]) 
    
            
    def isGoal(self,cur_state):
        """Judge if the current state has reached the goal state

        Args:
            cur_state (list): current state

        Returns:
            bool: if the current state has reached the goal state, return True else False
        """
        for p in self.pos:
            if p not in cur_state:
                return False
        for n in self.neg:
            if n in cur_state:
                return False
        return True
            
    def Astar(self):
        """A* search

        Returns:
            list: the optimal solution
            str: other args
        """
        frontier = queue.PriorityQueue()
        closed  = dict()
        frontier.put((0,0,0,self.state,[]))
        j = 0
        cnt = 0
        while not frontier.empty():
            cnt+=1
            top = frontier.get()
            cur_state = tuple(sorted((top[-2])))
            nsco = top[0]
            path = top[-1]
            #print(cnt)
            if cur_state in closed and nsco > closed[cur_state]:
                continue
            closed.update({cur_state: nsco})
            if self.isGoal(cur_state):
                return path,"\nA optimal solution " + str(len(path)) + " moves\n" + "Nodes generated during search: " + str(j) +"\nNodes expanded during search: " + str(cnt)
            nei = self.get_neigh(deepcopy(path),list(cur_state))
            for n in nei:
                if tuple(sorted(n[-2])) not in closed:
                    j+=1
                    frontier.put((n[0],n[1],j,n[2],n[3]))    
        return "Error!"

#-----------------------------------------------
# Main
#-----------------------------------------------    
def main():
    #test_num = input("input the testcase number: ")
    time_start=time.time()
    domain = sys.argv[1]
    problem = sys.argv[2]
    action,prob = initial(domain,problem)
    planner = STRIPS_Planner(action,prob)
    plan = planner.Astar()
    print("\nFound Plan:")
    for act in plan[0]:
        print(act[0],end=' ')
        for i in act[1]:
            print(act[1][i],end=' ')
        print()
    print(plan[1])
    time_end=time.time()
    print('Total time: ',time_end-time_start,'s',sep='') #此处单位为秒
    




main()