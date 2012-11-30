#!/usr/bin/python

import random
import time
import sys

## heuristics implemented:
##+ 1. miss(x) => x != y_1 /\ x != y_2 /\ ... /\ x != y_n where {y_i} = L1 before miss
##+ 2. L_i has clique with 5 elements => unsat
##+ 3. L_i has clique with 4 elements and some x != y_1 /\ x != y_2 /\ ... /\ x != y_{w-1} with {y_i} = this clique => x == y_w
##+ 4. template has miss/hit/any(x) and after that miss/any(x_w) and then miss(x) and {x_1, x_2, ..., x_n} - literally different addresses between these memory accesses =>
##	if n < w then unsat
##	if n == w then any(x_w) == miss(x_w) and all {x, x_1, x_2, ..., x_w} pairly different !!!
##+ 5. any(x) --> hit(x) if x in L_i before any(x)
##  6. any(x) and L from this any(x) has a clique4 and x ~isin this clique4  => any(x) == hit(x)
##+ 7. miss(x) and then hit(y) and x != y then  add y to addresses _before_ miss(x)

def traverse_c(program, l1, equals, not_equals) :
	for l in l1 :
		assert isinstance(l, int)
	
	for i in range(len(l1)) :
		for j in range(len(l1)) :
			if j > i :
				assert l1[j] != l1[i]
	# try to solve
	l0 = ["_" + str(j) for j in range(len(l1))]
        
	not_equals_l0 = [[l0[k], l0[j]] for j in range(len(l1))
                                         for k in range(j+1, len(l1))]
                
	equals_l0 = [[l, l] for l in l0]

	nums = [j for j in 
                        l0 +
                        [i["addr"] for i in program if "addr" in i] +
                        [i["remvd"] for i in program if "remvd" in i]
		if isinstance(j, int)]
                
	not_equals_nums = [[nums[k], nums[j]] for k in range(len(nums))
                                           for j in range(k+1, len(nums))]
                
	
	# try heuristics: 1 (may infer some inequalities and add them to not_equals)
	while True :
		print("heuristic 1: addresses in states of L1")
		addrs = reachable_addresses(program, len(l0), equals, not_equals)
		print("ADDRS = ", addrs)
		if not sat(equals, not_equals) :
			return False
		print("heuristic 1.2: search for cliques5")
		for ads in addrs :
			if len(cliques(ads, len(l1) + 1, equals, not_equals)) > 0 :
				return False
		print("NOT_EQUALS: ", not_equals)
		if not sat(equals, not_equals) :
			return False
	
		print("heuristic 1.3 : infer equalities from cliques4")
		if infer(addrs, equals, not_equals) :
			if not sat(equals, not_equals) :
				return False
			continue

		print("infer all_diffs")
		if infer_alldiffs(program, len(l1), equals, not_equals) :
			print("INFERRED!!! not_equals = ", not_equals)
			if not sat(equals, not_equals) :
				return False
			continue

#		print("NOT INFER :(")
		break
	

	# try heuristics: 2
	print("heuristic 2")
	eq = equals + equals_l0
	neq = not_equals + not_equals_l0 + not_equals_nums
	remvd_neqs(program, l1, eq, neq)  # equals and not_equals may be increased
	if not sat(eq, neq) :
		return False
	
	print("backtracking")
	if not traverse(program, l0, eq, neq) :
		return False


        # minimize solution
	print("TRYING TO MINIMIZE SOLUTION")
	for i in range(len(l1)+1) :
		l0 = []
		for j in range(i) :
			l0 += ["_" + str(j)]
		for j in range(len(l1) - i) :
			l0 += [l1[j]]
		
		assert len(l0) == len(l1)

		not_equals_l0 = []
                
		for j in range(len(l1)) :
			for k in range(len(l1)) :
				if k > j :
					not_equals_l0 += [[l0[k], l0[j]]]
		
		equals_l0 = []
		for l in l0 :
			equals_l0 += [[l, l]]
                
		nums = [j for j in 
				l0 +
				[i["addr"] for i in program if "addr" in i] +
				[i["remvd"] for i in program if "remvd" in i]
		if isinstance(j, int)]
                
		not_equals_nums = []
		for j in nums :
			for k in nums :
				if k != j :
					not_equals_nums += [[k, j]]
                
		# try heuristics
		eq = equals + equals_l0
		neq = not_equals + not_equals_l0 + not_equals_nums
		remvd_neqs(program, l1, eq, neq)  # equals and not_equals may be increased
		if sat(eq, neq) :
			if traverse(program, l0, eq, neq) :
				return True
	
	return False


def traverse(program, l1, equals, not_equals):
	assert len(l1) == 4

	for i in range(len(l1)) :
		for j in range(len(l1)) :
			if j > i :
				assert l1[i] != l1[j]


	if len(program) == 0 :
		print_model(equals, not_equals)
		return True

#	print(" ")
#	print("left: ", len(program), "program elements")
#	print("cache:", l1)

	addr = program[0]["addr"];

	if "l1" in program[0] :
		if program[0]["l1"] == "miss" :
#			print("try miss(", addr, ")")
			neq = not_equals + [[addr, x] for x in l1]
			eq = [[program[0]["remvd"],l1[-1]]] if "remvd" in program[0] else []
			
#			if "remvd" in program[0] :
#				print("remvd: ", program[0]["remvd"], "=", l1[-1])

			if False and len(program) == 1 :
				print("TRY SAT:")
				print("EQ = ", equals + eq)
				print("NotEQ = ", neq)
			
			if sat(equals+eq, neq) :
				return traverse(
					program[1:],
					[addr] + l1[:-1],
					equals + eq,
					neq)

		if program[0]["l1"] == "hit" :
			ind = index(addr, l1, equals)
			if ind != -1 :
				if traverse(program[1:], [addr] + l1[:ind] + l1[ind+1:], equals, not_equals) :
					return True
			else :
				for i in range(len(l1)) :
					e = l1[i]
#					print("try hit: ", addr, "=", e)
					if sat(equals + [[addr, e]], not_equals) :
						if traverse(
							program[1:],
							[e] + l1[:i] + l1[i+1:], 
							equals + [[addr, e]],
							not_equals) :
							return True
#					else :
#						print("unsat; try next or backtrack")

		if program[0]["l1"] == "any" :
			program[0]["l1"] = "miss"
			if traverse(program, l1, equals, not_equals) :
				return True
			program[0]["l1"] = "hit"
			if traverse(program, l1, equals, not_equals) :
				return True
			program[0]["l1"] = "any"

#		print("backtrack")	
		return False
				
	else :
		return traverse(program[1:], l1, equals, not_equals)

########################################

def sat(equals, not_equals) :
	# assert equals is a list of pairs (a pair is a list of 2 elements)
	for eq in equals :
		assert len(eq) == 2
	# assert not_equals is a list of pairs
	for neq in not_equals :
		assert len(neq) == 2

	

	for c in not_equals :
		if exists_path(c[0], c[1], equals) :
			return False
	return True

def exists_path(start, finish, edges) :
	if start == finish :
		return True

	for edge_n in range(len(edges)) :
		edge = edges[edge_n]
		edges_without = edges[:edge_n] + edges[edge_n+1:]
		if start == edge[0] and exists_path(edge[1], finish, edges_without) :
			return True
		elif start == edge[1] and exists_path(edge[0], finish, edges_without) :
			return True
	return False	


def index(addr, l1, eqs) :
	for i in range(len(l1)) :
		if eq(addr, l1[i], eqs) :
			return i
	return -1

def eq(x, y, eqs) :
	return exists_path(x, y, eqs)

def print_model(equals, not_equals) :
	elems_classes = get_eqclasses(equals)
	# elems_classes is a list of sets

	if len(elems_classes) == 0 :
		print("elems_classes is empty :( nothing to print")

	values = {}
	used_values = []
	second_classes = []
	for eq_class in elems_classes :
		# eq_class is a set
		ints = [x for x in eq_class if isinstance(x, int)]
		if len(ints) > 0 :
			value = ints[0]
			used_values += [value]
			for a in eq_class :
				if not isinstance(a, int) :
					values[a] = value
		else :
			second_classes += [eq_class]
	
	if len(used_values) > 0 :
		value = max(used_values) + 1
	else :
		value = 0

	for eq_class in second_classes :
		for a in eq_class :
			values[a] = value
		value = value + 1

	for a in values :
		print(a, '=', values[a])
			
##################################################

# gets a list of pairs (a pair is a list of 2 values)
# returns a list of equivalence classes (eqclass is a set of values) 
def get_eqclasses(equals) :
	if len(equals) == 0 :
		return []
	
	prevpairs = []
	newpairs = [equals[0]]
	while newpairs != prevpairs :
		eqclass = set([i for p in newpairs for i in p])
		prevpairs = newpairs
		newpairs = [p for p in equals
					if p[0] in eqclass 
					or p[1] in eqclass ]
	return [eqclass] + get_eqclasses([p for p in equals if p not in newpairs])

#################################################

def remvd_neqs(program, l1, equals, not_equals) :
	w = len(l1)

	for i in range(len(program)) :
		if "remvd" in program[i] :
			rmvd_adr = program[i]["remvd"]
			in_l1 = []
			remvd_l1 = []
			j = i-1
			while j >= 0 and len(in_l1) < w-1 :
				if "l1" in program[j] :
					if not is_known(program[j]["addr"], in_l1, equals) :
						in_l1 += [program[j]["addr"]]
					if "remvd" in program[j] :
						remvd_l1 += [program[j]["remvd"]]
				j = j - 1

			if len(in_l1) < w-1:
				k = 0
				while len(in_l1) < w - 1 :
					if not is_known(l1[k], in_l1, equals) :
						in_l1 += [l1[k]]
					k += 1

			not_equals += [[rmvd_adr, a] for a in in_l1 + remvd_l1]
													

def is_known(x, l, equals) :
	if x in l : return True

	for i in l :
		if exists_path(x, i, equals) :
			return True
	return False

#################################################

def reachable_addresses(program, w, equals, not_equals) :
	result = []
	addresses = []
#	print("START")
	for i in range(len(program)) :
#		print("i = ", i)
		if program[i]["l1"] == "hit" :
			if not is_known(program[i]["addr"], addresses, equals):
				addresses += [program[i]["addr"]]
		elif program[i]["l1"] == "any" and is_known(program[i]["addr"], addresses, equals) :
			program[i]["l1"] = "hit"
		else :
#			print("PUSH: ", addresses)
			addr = program[i]["addr"]
			if program[i]["l1"] == "miss" :
				for a in addresses :
					if ([addr, a] not in not_equals) and ([a, addr] not in not_equals) :
						not_equals += [[a, addr]]
			if not sat(equals, not_equals) :
				return []
#			print("1.1")
			for j in range(i+1, len(program)) :
				if program[j]["l1"] != "hit" : break
				a = program[j]["addr"]
#				print("1.1.1")
#				print("equals: ", equals)
#				print("not_equals: ", not_equals)
				if always_different(a, addr, equals, not_equals) :
#					print("1.1.2")
					if not is_known(a, addresses, equals) :
#						print("1.1.3")
						addresses += [a]
						if ([addr, a] not in not_equals) and ([a, addr] not in not_equals) :
						 	not_equals += [[a, addr]]

#			print("1.2")
			if len(addresses) > 0 :
				result += [addresses]
			
			addresses = [program[i]["addr"]]
			j = i
			while j >= 0 and len(addresses) < w :
				if is_known(program[j]["addr"], addresses, equals) :
					pass
				else :
					addresses += [program[j]["addr"]]
				j -= 1
				
			# addresses = [program[j]["addr"] for j in range(max(0,i-w+1), max(0,i+1))]
#			print("ADDRESSES := ", addresses)
			# TODO: add to "addresses" more addresses if has equals
			# TODO: add "remvd"s to "addresses"
	
	if len(addresses) > 0 :
#		print("PUSH: ", addresses)
		result += [addresses]
#	print("FINISH: ", result)
	return result

def cliques(addresses, size, equals, not_equals) :
	if len(addresses) < size :
		return []

	result = []
	print("addresses: ", addresses)
	print("size: ", size)
	for i1 in range(len(addresses) - size + 1) :
		print("try: i1 =", i1)
		for i2 in range(i1+1, len(addresses) - size+2) :
			print("	try: i2 =", i2)
			if always_different(addresses[i1], addresses[i2], equals, not_equals) :
				if size == 2 :
					result += [[addresses[i1], addresses[i2]]]
					continue
			else:
				continue
			for i3 in range(i2+1, len(addresses) - size + 3) :
				print("		try: i3 =", i3)
				if always_different(addresses[i1], addresses[i2], equals, not_equals) and (
				    always_different(addresses[i3], addresses[i2], equals, not_equals) ) :
					if size == 3 :
						result += [[addresses[i1], addresses[i2], addresses[i3]]]
						continue
				else :
					continue
				for i4 in range(i3+1, len(addresses) - size + 4) :		
					print("				try: i4 =", i4)
					if always_different(addresses[i4], addresses[i1], equals, not_equals) and (
					  always_different(addresses[i4], addresses[i2], equals, not_equals) ) and (
					  always_different(addresses[i4], addresses[i3], equals, not_equals) ) :
						if size == 4 :
							result += [[addresses[i1], addresses[i2], addresses[i3], addresses[i4]]]
							continue
					else :
						continue
					for i5 in range(i4+1, len(addresses) - size + 5) :
						print("					try: i5 =", i5)
						if always_different(addresses[i5], addresses[i1], equals, not_equals) and (
						always_different(addresses[i5], addresses[i2], equals, not_equals) ) and (
						always_different(addresses[i5], addresses[i3], equals, not_equals) ) and (
						always_different(addresses[i5], addresses[i4], equals, not_equals) ) :
							if size == 5 :
								result += [[addresses[i1], addresses[i2], addresses[i3], addresses[i4], addresses[i5]]]
	return result

def always_different(x, y, equals, not_equals) :
	for n_eq in not_equals :
		if exists_path(x, n_eq[0], equals) and exists_path(y, n_eq[1], equals) or (
		   exists_path(x, n_eq[1], equals) and exists_path(y, n_eq[0], equals) ) :
			return True
	return False

###############################################

def infer(addresses, equals, not_equals) :
	result = False
	for adrs in [s for s in addresses if len(s) > 4] :
		print("see: ", adrs)
		for clique in cliques(adrs, 4, equals, not_equals) :
			print("clique: ", clique)
			print("so tryes: ", [x for x in adrs if x not in clique])
			for a in [x for x in adrs if x not in clique] : # for a in (adrs - clique)
				print("a = ", a)
				values = maybe_equal(clique, a, equals, not_equals)
				print("so ", a, "may be equal to ", values)
				if values is not None and len(values) == 1 :
					if ([values[0], a] not in equals) and ([a, values[0]] not in equals) :
						equals += [[values[0], a]]
					print("INFER !!! ", values[0], " = ", a)
					result = True
#		else :
#			print("no cliques :(")
	print("all seen :)")
	return result

def maybe_equal(addresses, addr, equals, not_equals) :
	print("maybe_equal: equals: ", equals)
	print("maybe_equal: not_equals: ", not_equals)
	result = []
	for a in addresses :
		if not always_different(a, addr, equals, not_equals) :
			result += [a]
	return result

##################################################

def infer_alldiffs(program, w, equals, not_equals) :  # returns (is_inferred : bool)
	
	inferred = False

	for i in reversed([i for i in range(len(program))
					if program[i]["l1"] == "miss" ]) :

		seen = []
		for j in reversed(range(i)) :
			if program[j]["addr"] in seen : continue
			seen += [program[j]["addr"]]

			
			if exists_path(program[i]["addr"], program[j]["addr"], equals) :
				print("find hit --> miss: ", program[i]["addr"])
				addresses = maybe_differents([program[k]["addr"] for k in range(j+1, i)], equals, not_equals)
				print("addresses = ", addresses)
				if len(addresses) < w :
					not_equals += [[program[i]["addr"], program[i]["addr"]]]  # unsat
					return True
				elif len(addresses) == w :
					if program[i-1]["l1"] == "hit" :
						not_equals += [[program[i]["addr"], program[i]["addr"]]] # unsat
						return True
					else :
						program[i-1]["l1"] = "miss"
						for i1 in range(len(addresses)) :
							for i2 in range(i1+1, len(addresses)) :
								a1 = addresses[i1]
								a2 = addresses[i2]
								if ([a1, a2] not in not_equals) and ([a2, a1] not in not_equals) :
									not_equals += [[a1, a2]]
									inferred = True
				else :  # len(addresses) > w  # TODO
					pass
					

	return inferred

def maybe_differents(addresses, equals, not_equals) :
	
	if len(addresses) < 2 : return addresses

	result = [addresses[0]]

	for i in range(1, len(addresses)) :
		if not is_known(addresses[i], result, equals) :
			result += [addresses[i]]

	return result


#################################################

def run(length) :
	template = []
	for i in range(length) :
		situation = ["hit", "miss", "any"][random.randrange(3)]
		variable = "a" + str(random.randrange(length))
		template += [{"l1" : situation, "addr" : variable}]

	
	equals = [[i["addr"], i["addr"]] for i in template]

	not_equals = [["a" + str(i), "a" + str(j)] for i in range(1, 6) for j in range(i+1, 6)]

	print("TEMPLATE: ")
	for x in template:
		print(x)
	if not traverse_c(template, [1, 2, 3, 4], equals, not_equals) :
		print("unsat")
		return False
	else :
		return True


if len(sys.argv) > 1 :
	
	unsat_min = 1000
	unsat_max = 0
	sat_min = 1000
	sat_max = 0

	count = 0
	unsats = 0
	sats = 0
	sum_unsats = 0
	sum_sats = 0

	while True :
		start = time.time()
		c = run(10)
		stop = time.time()
		duration = stop - start
		print(duration)

		if c :
			sat_min = min(sat_min, duration)
			sat_max = max(sat_max, duration)
			sum_sats += duration
			sats += 1
		else :
			unsat_min = min(unsat_min, duration)
			unsat_max = max(unsat_max, duration)
			sum_unsats += duration
			unsats += 1

		if count == 10 :
			count = 0
			print("================================")
			print("  SAT : ", sat_min, "..", sat_max)
			print("		average = ", 0 if sats == 0 else sum_sats / sats)
			print("UNSAT : ", unsat_min, "..", unsat_max)
			print("		average = ", 0 if unsats == 0 else sum_unsats / unsats)
			print("================================")
		else :
			count += 1

		if duration > 10 :
			if sys.argv[1] == "unsat" :
				if not c : exit(0)
			elif sys.argv[1] == "sat" :
				if c : exit(0)
			else :
				exit(0)

template1 = [{'addr': 'a2', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a3', 'l1': 'miss'},
{'addr': 'a1', 'l1': 'hit'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a4', 'l1': 'hit'},
{'addr': 'a4', 'l1': 'any'},
{'addr': 'a7', 'l1': 'miss'} ]

template1 = [ {'addr': 'a2', 'l1': 'hit'},
{'addr': 'a8', 'l1': 'hit'},
{'addr': 'a0', 'l1': 'any'},
{'addr': 'a7', 'l1': 'hit'},
{'addr': 'a9', 'l1': 'any'},
{'addr': 'a2', 'l1': 'miss'},
{'addr': 'a1', 'l1': 'miss'},
{'addr': 'a8', 'l1': 'miss'},
{'addr': 'a7', 'l1': 'hit'},
{'addr': 'a0', 'l1': 'hit'} ]

template1 = [
{'addr': 'a1', 'l1': 'hit'},
{'addr': 'a6', 'l1': 'miss'},
{'addr': 'a4', 'l1': 'any'},
{'addr': 'a6', 'l1': 'miss'},
{'addr': 'a6', 'l1': 'miss'},
{'addr': 'a6', 'l1': 'hit'},
{'addr': 'a1', 'l1': 'hit'},
{'addr': 'a6', 'l1': 'miss'},
{'addr': 'a0', 'l1': 'miss'},
{'addr': 'a2', 'l1': 'any'}
]

template1 = [
{'addr': 'a8', 'l1': 'hit'},
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a1', 'l1': 'hit'},
{'addr': 'a9', 'l1': 'hit'},
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a7', 'l1': 'hit'},
{'addr': 'a7', 'l1': 'any'},
{'addr': 'a0', 'l1': 'miss'},
{'addr': 'a3', 'l1': 'miss'}
] # unsat

template1 = [
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a4', 'l1': 'miss'},
{'addr': 'a1', 'l1': 'hit'},
{'addr': 'a9', 'l1': 'any'},
{'addr': 'a7', 'l1': 'miss'},
{'addr': 'a2', 'l1': 'miss'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a4', 'l1': 'hit'},
{'addr': 'a2', 'l1': 'any'}
]  # sat

template = [
{'addr': 'a9', 'l1': 'hit'},
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a8', 'l1': 'any'},
{'addr': 'a7', 'l1': 'hit'},
{'addr': 'a5', 'l1': 'miss'},
# {'addr': 'a1', 'l1': 'any' }, ###
{'addr': 'a9', 'l1': 'miss'},
{'addr': 'a4', 'l1': 'any'},
{'addr': 'a5', 'l1': 'hit'},
{'addr': 'a3', 'l1': 'hit'},
{'addr': 'a4', 'l1': 'any'}
]  # unsat

template3 = [
{'addr': 'a6', 'l1': 'any'},
{'addr': 'a0', 'l1': 'hit'},
{'addr': 'a0', 'l1': 'hit'},
{'addr': 'a8', 'l1': 'miss'},
{'addr': 'a0', 'l1': 'any'},
{'addr': 'a6', 'l1': 'hit'},
{'addr': 'a1', 'l1': 'hit'},
{'addr': 'a0', 'l1': 'hit'},
{'addr': 'a6', 'l1': 'any'},
{'addr': 'a7', 'l1': 'any'}
]  # sat

template2 = [
{'addr': 'a5', 'l1': 'any'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a5', 'l1': 'hit'},
{'addr': 'a4', 'l1': 'hit'},
{'addr': 'a0', 'l1': 'miss'},
{'addr': 'a7', 'l1': 'any'},
{'addr': 'a2', 'l1': 'miss'},
{'addr': 'a7', 'l1': 'hit'},
{'addr': 'a5', 'l1': 'hit'}
] # unsat

template3 = [
{'addr': 'a8', 'l1': 'miss'},
{'addr': 'a9', 'l1': 'hit'},
{'addr': 'a1', 'l1': 'hit'},
{'addr': 'a9', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a5', 'l1': 'hit'},
{'addr': 'a4', 'l1': 'any'},
{'addr': 'a8', 'l1': 'any'}
] # sat

template3 = [
{'addr': 'a6', 'l1': 'miss'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a0', 'l1': 'hit'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a6', 'l1': 'any'},
{'addr': 'a5', 'l1': 'any'},
{'addr': 'a9', 'l1': 'any'},
{'addr': 'a4', 'l1': 'miss'},
{'addr': 'a0', 'l1': 'miss'},
{'addr': 'a6', 'l1': 'hit'}
] # sat

template2 = [
{'addr': 'a0', 'l1': 'hit'},
{'addr': 'a4', 'l1': 'hit'},
{'addr': 'a7', 'l1': 'any'},
{'addr': 'a9', 'l1': 'miss'},
{'addr': 'a1', 'l1': 'hit'},
{'addr': 'a3', 'l1': 'miss'},
{'addr': 'a4', 'l1': 'miss'},
{'addr': 'a7', 'l1': 'hit'},
{'addr': 'a0', 'l1': 'hit'},
{'addr': 'a5', 'l1': 'miss'}
] # unsat

template2 = [
{'addr': 'a1', 'l1': 'hit'},
{'addr': 'a6', 'l1': 'miss'},
{'addr': 'a9', 'l1': 'miss'},
{'addr': 'a9', 'l1': 'any'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a7', 'l1': 'miss'},
{'addr': 'a3', 'l1': 'miss'},
{'addr': 'a0', 'l1': 'miss'},
{'addr': 'a6', 'l1': 'hit'},
{'addr': 'a9', 'l1': 'hit'}
] # unsat

template3 = [
{'addr': 'a2', 'l1': 'miss'},
{'addr': 'a5', 'l1': 'miss'},
{'addr': 'a0', 'l1': 'hit'},
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a2', 'l1': 'any'},
{'addr': 'a9', 'l1': 'any'},
{'addr': 'a2', 'l1': 'any'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a5', 'l1': 'miss'},
{'addr': 'a2', 'l1': 'any'}
]  # sat

template3 = [
{'addr': 'a4', 'l1': 'any'},
{'addr': 'a6', 'l1': 'hit'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a7', 'l1': 'hit'},
{'addr': 'a9', 'l1': 'hit'},
{'addr': 'a7', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'}
] # sat

template2 = [
{'addr': 'a2' , 'l1': 'any'},
{'addr': 'a3' , 'l1': 'any'},
{'addr': 'a7' , 'l1': 'miss'},
{'addr': 'a6' , 'l1': 'any'},
{'addr': 'a1' , 'l1': 'hit'},
{'addr': 'a5' , 'l1': 'miss'},
{'addr': 'a4' , 'l1': 'hit'},
{'addr': 'a9' , 'l1': 'miss'},
{'addr': 'a7' , 'l1': 'miss'},
{'addr': 'a6' , 'l1': 'any'}
] # unsat

template4 = [
{'addr': 'a5', 'l1': 'miss'},
{'addr': 'a7', 'l1': 'any'},
{'addr': 'a4', 'l1': 'miss'},
{'addr': 'a1', 'l1': 'miss'},
{'addr': 'a0', 'l1': 'miss'},
{'addr': 'a7', 'l1': 'hit'},
{'addr': 'a7', 'l1': 'any'},
{'addr': 'a2', 'l1': 'any'},
{'addr': 'a5', 'l1': 'hit'},
{'addr': 'a6', 'l1': 'miss'}
] # sat  # loop

template2 = [
{'addr': 'a0', 'l1': 'hit'},
{'addr': 'a8', 'l1': 'any'},
{'addr': 'a7', 'l1': 'hit'},
{'addr': 'a6', 'l1': 'hit'},
{'addr': 'a9', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a0', 'l1': 'hit'},
{'addr': 'a4', 'l1': 'miss'},
{'addr': 'a6', 'l1': 'miss'},
{'addr': 'a5', 'l1': 'miss'}
] # unsat

template2 = [
{'addr': 'a8', 'l1': 'hit'},
{'addr': 'a8', 'l1': 'hit'},
{'addr': 'a8', 'l1': 'miss'},
{'addr': 'a7', 'l1': 'hit'},
{'addr': 'a7', 'l1': 'miss'},
{'addr': 'a8', 'l1': 'hit'},
{'addr': 'a8', 'l1': 'miss'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a6', 'l1': 'any'},
{'addr': 'a8', 'l1': 'miss'}
] # unsat

template2 = [
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a3', 'l1': 'hit'},
{'addr': 'a3', 'l1': 'hit'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a8', 'l1': 'miss'},
{'addr': 'a8', 'l1': 'any'},
{'addr': 'a3', 'l1': 'miss'},
{'addr': 'a3', 'l1': 'hit'},
{'addr': 'a7', 'l1': 'any'}
] # unsat

template3 = [
{'addr': 'a6', 'l1': 'hit'},
{'addr': 'a1', 'l1': 'hit'},
{'addr': 'a6', 'l1': 'any'},
{'addr': 'a6', 'l1': 'any'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a6', 'l1': 'any'},
{'addr': 'a4', 'l1': 'any'},
{'addr': 'a6', 'l1': 'hit'},
{'addr': 'a6', 'l1': 'any'},
{'addr': 'a0', 'l1': 'hit'}
] # sat

template2 = [
{'addr': 'a0', 'l1': 'miss'},
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a3', 'l1': 'any'},
{'addr': 'a3', 'l1': 'hit'},
{'addr': 'a3', 'l1': 'miss'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a7', 'l1': 'miss'},
{'addr': 'a3', 'l1': 'hit'},
{'addr': 'a2', 'l1': 'miss'}
] # unsat

template = [
{'addr': 'a2', 'l1': 'miss'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a7', 'l1': 'miss'},
{'addr': 'a1', 'l1': 'any'},
{'addr': 'a2', 'l1': 'miss'},
{'addr': 'a2', 'l1': 'hit'},
{'addr': 'a2', 'l1': 'any'},
{'addr': 'a6', 'l1': 'hit'},
{'addr': 'a5', 'l1': 'miss'}
] # unsat

# lru element is the last element of this seq
initial_l1 = [1, 2, 3, 4]

equals = []
for i in template :
	if [i["addr"], i["addr"]] not in equals : equals += [[i["addr"],i["addr"]]]

# alldiffs_l1 = [ [initial_l1[i], initial_l1[j]]
#			for i in range(len(initial_l1))
#			for j in range(len(initial_l1))
#			if j > i ]

# not_equals = [["a1", "a2"], ["a2", "a3"], ["a3", "a4"]]
# not_equals = [["a1", "a2"], ["a1", "a3"], ["a1", "a4"],
#				["a2", "a3"], ["a3", "a4"]]

not_equals = [["a1", "a2"], ["a1", "a3"], ["a1", "a4"],
			["a2", "a3"], ["a2", "a4"], ["a3", "a4"]
		,["a1", "a5"],["a2", "a5"],["a3", "a5"],["a4", "a5"]]

if not traverse_c(template, initial_l1, equals, not_equals ) :
	print("template is unsatisfiable")

