from collections import defaultdict
from pysmt.shortcuts import *

class UnsatValueError(Exception):
    pass

class IntModel:
    def __init__(self, data):
        self.persons = data["persons"]
        self.person_ids = range(len(self.persons))
        self.person2person_id = { k: v for k, v in enumerate(self.persons) }
        self.tables = data["tables"]
        self.table_ids = range(len(self.tables))
        self.groups = data["groups"]
        self.friends = data["friends"]
        self.couples = data["couples"]
        self.enemies = data["enemies"]        
        
    def __get_person_int(self, p_id):
        return Symbol('p{}'.format(p_id), INT)
    
    def __get_person_id_constraint(self, p_id):
        p = self.__get_person_int(p_id)
        return And(p >= 0, p <= self.table_ids[-1])
        
    def __get_table_id_constraint(self, t_id):
        t_cap = self.tables[t_id]
        ps = map(self.__get_person_int, self.person_ids)
        return Plus(map(lambda p: Ite(Equals(p, Int(t_id)), Int(1), Int(0)), ps)) <= t_cap

    def __get_couple_constraint(self, (c1, c2)):
        c1p = self.__get_person_int(c1)
        c2p = self.__get_person_int(c2)
        return Equals(c1p, c2p)

    def __get_enemy_constraint(self, (e1, e2)):
        e1p = self.__get_person_int(e1)
        e2p = self.__get_person_int(e2)
        return Not(Equals(e1p, e2p))
    
    def __get_friend_constraint(self, friend):
        constraints = []

        for p, p_friends in self.friends.items():
            p_int = self.__get_person_int(p)
            if len(p_friends) > 1:
                for t in self.table_ids:
                    friend_ints = map(self.__get_person_int, p_friends)
                    ge_2_friends = Plus(map(lambda f: Ite(Equals(f, Int(t)), Int(1), Int(0)), friend_ints)) >= 1
                    constraints.append(Implies(Equals(p_int, Int(t)), ge_2_friends))
            elif len(p_friends) > 0:
                c_cons = self.__get_couple_constraint((p, p_friends[0]))
                constraints.append(c_cons)
            
        return And(constraints)
    
    def __get_groups_constraint(self, t):
        constraints = []
        t_cap = self.tables[t]
        group_cap = int(t_cap * 0.7)
        affected_groups = { k: v for k, v in self.groups.items() if len(v) > group_cap }
        for g, g_members in affected_groups.items():
            g_member_ints = self.get_persons_int(g_members)
            g_members_on_t = Plus(map(lambda g: Ite(Equals(g, Int(t)), Int(1), Int(0)), g_member_ints))
            cons = g_members_on_t <= group_cap
            constraints.append(cons)
            
        return And(constraints)
        
    def get_constraint(self):
        constraints = [
            And(map(self.__get_person_id_constraint, self.person_ids)),
            And(map(self.__get_table_id_constraint, self.table_ids)),
            And(map(self.__get_couple_constraint, self.couples)),
            And(map(self.__get_enemy_constraint, self.enemies)),
            And(map(self.__get_friend_constraint, self.friends)),
            And(map(self.__get_groups_constraint, self.table_ids)),
        ]
        
        return And(map(And, constraints))
    
    def solve(self, constraint, solver_name):
        solution = get_model(constraint, solver_name=solver_name)
        if solution is None:
            raise UnsatValueError("unable to satisfy model")
        
        assignment = [solution.get_py_value(self.__get_person_int(x)) for x in self.person_ids]
        return assignment


class WeddingOptimizer:
    data = {}
    config = {
        "solver": "yices",
        "model": IntModel,
    }

    def __init__(self, data, config={}):
        self.data = data
        self.config.update(config)
        self.__validate_data()
        self.__process_data()
        
    def __validate_data(self):
        pass
    
    def __process_data(self):
        friends_set = defaultdict(set)
        for _, g_members in self.data["groups"].items():
            for member in g_members:
                friends_set[member] = friends_set[member].union(g_members)

        friends = defaultdict(list)
        for p, p_friends in friends_set.items():
            friends[p] = list(p_friends.difference(set([p])))
        
        self.data["friends"] = friends
    
    def solve(self):
        model = self.config["model"](self.data)
        constraint = model.get_constraint()
        return model.solve(constraint, self.config['solver'])
