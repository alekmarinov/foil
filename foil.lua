-- Sollution limits
-- 1. P(X1,X2,...,Xn):-P(X1,X2,...,Xn)
-- 2. P(X1,X2,...,Xn):-...,Pk(Xi1,Xi2,...,Xin), ako sushtestviva Xk (- {Xi1,Xi2,...,Xin} i Xk e nesvurzan

RULES_LIMIT		=	10;
CONSTRAINTS_LIMIT	=	20;

dofile("Clonable.lua");
dofile("Example.lua");

math.log2=function(x)
	return math.log10(x)/math.log10(2);
end

_Constraint=Clonable();
_Rule=Clonable();
_Foil=Clonable();

-- Class Constraint

function _Constraint:addArgument(argName)
	table.insert(self.args, argName);
end

function _Constraint:negate()
	self.negative=not self.negative;
end

function _Constraint:getName()
	return self.name;
end

function _Constraint:isNegative()
	return self.negative;
end

function _Constraint:getArguments()
	return self.args;
end

function _Constraint:getArgument(k)
	return self.args[k];
end

function _Constraint:isEqual()
	if self.name == "=" then
		return 1;
	end
end

function _Constraint:equalTo(constraint)
	if self:getName() == constraint:getName() then
		-- compare args
		local match=true;
		table.foreachi(self:getArguments(), function(k, arg)
			if arg~=constraint:getArgument(k) then
				match=false
			end
		end);
		return match;
	end
	return false;
end

function Constraint(name)
	local t=_Constraint:clone();
	t.negative=false;
	t.name=name;
	t.args={};
	return t;
end

-- Class Rule

function _Rule:getName()
	return self.name;
end

function _Rule:addConstraint(constraint)
	table.insert(self.constraints, constraint);
end

function _Rule:removeLastConstraint()
	table.remove(self.constraints);
end

function _Rule:getArity()
	return self.arity;
end

function _Rule:getArguments()
	return self.args;
end

function _Rule:isExistConstraint(constraint)
	local isExist=false;
	table.foreachi(self.constraints, function(_, eachConstraint)
		if eachConstraint:equalTo(constraint) then
			isExist=true;
			return 1;
		end
	end);
	return isExist;
end

function _Rule:getConstraints()
	return self.constraints;
end

function Rule(name, arity)
	local t=_Rule:clone();
	local i;
	t.name=name;
	t.arity=arity;
	t.args={};
	t.constraints={};
	for i=1,arity do
		table.insert(t.args, "X"..i); 
	end
	return t;
end

-- Class Foil

-- generates all candidate literals (constraints)
function _Foil:gen_candidate_literals(rule, example)
	function permutations(perms, count, arr, append)
		local add_perm = function(app)
			local new_a={};
			table.foreachi(app, function(i, a)
				if i<=count then
					table.insert(new_a, a);
				end
			end);
			-- check if this perm is not already inserted
			local inserted=false;
			table.foreachi(perms, function(_, perm)
				-- check each value
				local match=true;
				table.foreachi(perm, function(i, p)
					if p ~= new_a[i] then
						match=false;
						return 1;
					end
				end);
				if match then
					inserted=true;
					return 1;
				end
			end);
			if not inserted then
				table.insert(perms, new_a);
			end
		end
		append=append or {};
		local len=table.getn(arr);
		if len>0 then
			local i, j;
			for i=1,len do	
				local arr1={};
				local cnt, cnt2;
				cnt=1; cnt2=1;
				while cnt<=len do
					if cnt==i then
						cnt2=cnt2+1;
						arr1[cnt]=arr[cnt2];
					else
						arr1[cnt]=arr[cnt2];
					end
					cnt=cnt+1; 
					cnt2=cnt2+1; 
				end
				local alen=table.getn(append);
				append1={};
				for j=1,table.getn(append) do
					append1[j]=append[j];
				end
				append1[alen+1]=arr[i];
				permutations(perms, count, arr1, append1);
			end
		else
			add_perm(append);
		end
	end
	
	local literals={};
	local arity=rule:getArity();
	local var_count=arity+arity-1;
	local vars={};
	local i,j,sign;
	for i=1,var_count do
		table.insert(vars, "X"..i);
	end
	local skip_general_predicate=false;
	local skip_once=false;
	for sign=1,2 do
	-- I. predicates
		table.foreachi(example:getPredicates(), function(_, predicate)
			local perms={};
			permutations(perms, example:getArity(predicate), vars);
			table.foreachi(perms, function(_, p)
				local literal=Constraint(predicate);
				table.foreachi(p, function(_, arg)
					literal:addArgument(arg);
				end);
				if sign==2 then
					literal:negate();
				end
				if not skip_general_predicate then
					if predicate == rule:getName() then
						skip_general_predicate=true;
						skip_once=true;
					end
				end
				if not skip_once then
					if not rule:isExistConstraint(literal) then
						table.insert(literals, literal);
					end
				end
				skip_once=false;
			end);
		end);
	-- II. equals
		for i=1,var_count-1 do
			for j=i+1,var_count do
				local literal=Constraint("=");
				literal:addArgument("X"..i);
				literal:addArgument("X"..j);
				if sign==2 then
					literal:negate();
				end
				if not rule:isExistConstraint(literal) then
					table.insert(literals, literal);
				end
			end
		end
	end
	return literals;
end

-- calc constraint gain
function _Foil:foil_gain(constraint, rule, positives, negatives, example)
	function concat_tables(table1, table2)
		local new_table={};
		table.foreachi(table1, function (_, v)
			table.insert(new_table, v);
		end);
		table.foreachi(table2, function (_, v)
			table.insert(new_table, v);
		end);
		return new_table;
	end
	local new_rule=rule:clone();
	local all_examples=concat_tables(positives, negatives);
	local pos0, neg0=self:check_rule(new_rule, all_examples, example);
	new_rule:addConstraint(constraint);
	local pos1, neg1=self:check_rule(new_rule, all_examples, example);
	-- calc t
	local t=0;
	table.foreachi(pos0, function(_, v0)
		table.foreachi(pos1, function(_, v1)
			local vals0=v0.value;
			local vals1=v1.value;
			local iseq=true;
			table.foreachi(vals0, function(i, _)
				if vals0[i]~=vals1[i] then
					iseq=false;
					return 1;
				end
			end);
			if iseq then
				t=t+1;
			end
		end);
	end);
	local p0, n0, p1, n1 = table.getn(pos0), table.getn(neg0), table.getn(pos1), table.getn(neg1);
	if p1==0 or p0 == 0 or p1+n1==0 or p0+n0==0 then return 0; end
	return t*(math.log2(p1/(p1+n1)) - math.log2(p0/(p0+n0)));
end

-- return constraints sorted by gain
function _Foil:max_foil_gain(constraints, rule, positives, negatives, example, isFirst)
	local maxGain;
	maxGain=-9999999;
	local gains={};
	table.foreachi(constraints, function(i, constraint)
		-- first constraint must be different than the predicate
		if not isFirst or constraint:getName() ~= rule:getName() then
			local gain=self:foil_gain(constraint, rule, positives, negatives, example);
			table.insert(gains, {ind=i, gain=gain, constraint=constraint});
			if gain>maxGain then
				maxGain=gain;
			end
		end
	end);
	-- sort constraints by gain and move positives first
	table.sort(gains, function(a, b)
		return a.gain>b.gain or (a.gain==b.gain and (a.constraint:isNegative() and 0 or 1)>(b.constraint:isNegative() and 0 or 1));
	end);
	local sorted_constraints={};
	table.foreachi(gains, function(_, g)
		table.insert(sorted_constraints, constraints[g.ind]);
	end);
	return sorted_constraints;
end

-- foil algorithm against to a given example
function _Foil:process(example)
	-- substracts two example sets
	function substract_examples(ex1, ex2)
		local result={};
		table.foreachi(ex1, function(_, e1)
			local global_match=false;
			table.foreachi(ex2, function(_, e2)
				-- check values
				local match=true;
				table.foreachi(e1.value, function(i, v)
					if v~=e2.value[i] then
						match=false;
					end
				end);
				if match then
					global_match=true;
					return 1;
				end
			end);
			if not global_match then
				table.insert(result, e1);
			end
		end);
		return result;
	end
	
	function copy_table(t)
		local new={};
		table.foreach(t, function(i, v)
			new[i]=v;
		end);
		return new;
	end

	local positives, negatives=example:splitExamples();
	local learned_rules={};

	while table.getn(positives)>0 do
		-- Learn new rule (without constraints)
		local rule=Rule(example:getTargetAttribute(), example:getTargetArity());
		
		local neg_covered=copy_table(negatives);
		local candidate_literals=self:gen_candidate_literals(rule, example);
		local isFirst=true;
		while table.getn(neg_covered)>0 do
			local constraints=self:max_foil_gain(candidate_literals, rule, positives, neg_covered, example, isFirst);
			isFirst=false;
			if table.getn(constraints)==0 then
				print("Sorry! Unable to find new constraint for rule:");
				print_rule(rule);
				os.exit();
			end
			
			-- choose the best constraint
			-- the alg. below check if the constraint is the last for the current rule
			-- and choose the first constraint from the sorted list which haven't any 
			-- unbound variables.
			
			-- cleaner but not the best realization is just to set constraint=constraints[1]
			local i;
			local l=table.getn(constraints);
			local constraint;
			local new_neg_covered;
			local found=false;
			for i=1,l do
				constraint=constraints[i];
				
				if not rule:isExistConstraint(constraint) then
					rule:addConstraint(constraint);
					_, new_neg_covered=self:check_rule(rule, neg_covered, example);
					-- last constraint?
					if table.getn(new_neg_covered)==0 then
						-- yes
						local vars={};
						local j;
						table.foreachi(rule:getArguments(), function(_, arg)
							vars[arg]=1;
						end);
						for j=1,table.getn(rule:getConstraints())-1 do
							table.foreachi(rule:getConstraints()[j]:getArguments(),
							function(_, arg)
								vars[arg]=true;
							end);
						end
						local hasUnbounds=false;
						table.foreachi(rule:getConstraints()[table.getn(rule:getConstraints())]:getArguments(), function(_, arg)
							if not vars[arg] then
								hasUnbounds=true;
								return 1;
							end
						end);
						if not hasUnbounds then
							found=true;
						end
					else
						found=true;
					end
					rule:removeLastConstraint();
					if found then
						break;
					end
				end
			end

			neg_covered=new_neg_covered;
			rule:addConstraint(constraint);
			if table.getn(rule:getConstraints()) > self.constraints_limit then
				break;
			end
		end
		table.insert(learned_rules, rule);
		local pos_covered, _=self:check_rule(rule, positives, example);
		positives=substract_examples(positives, pos_covered);
		if table.getn(learned_rules) > self.rules_limit then
			break;
		end
	end
	return learned_rules;
end

-- simple prolog mechanism evaluating a sequece of constraints againt an example 
-- starting with specified context:var_name->value
function _Foil:check_constraints(context, constraint_no, constraints, example)
	local constraint=constraints[constraint_no];
	if not constraint then
		-- return true if all contraints passed
		return true;
	end
	local temp_args={};
	if constraint:isEqual() then
		table.foreachi(constraint:getArguments(), function(i, arg)
			table.insert(temp_args, context[arg]);
		end);
		-- arity must be 2 for equal operation
		if temp_args[1] and temp_args[1] then
			if temp_args[1] == temp_args[2] then
				return not constraint:isNegative();
			else
				return constraint:isNegative();
			end
		else
			return false;
		end
	else
		local predicateExamps=example:getExamples(constraint:getName());
		local unbound_indeces={};
		table.foreachi(constraint:getArguments(), function(i, arg)
			table.insert(temp_args, context[arg]);
			if not context[arg] then
				table.insert(unbound_indeces, i);
			end
		end);
		
		local match=false;
		table.foreachi(predicateExamps, function(_, predExamp)
			if predExamp.bool == not constraint:isNegative() then
				match=true;
				table.foreachi(predExamp.value, function(i, val)
					if temp_args[i] and temp_args[i]~=val then
						match=false;
						return 1;
					end
				end);
				if match then
					local new_context={};
					table.foreach(context, function(i,v)
						new_context[i]=v;
					end);
					-- unificate unbound variables
					table.foreachi(unbound_indeces, function(_, ind)
						new_context[constraint:getArgument(ind)]=predExamp.value[ind];
					end);
					match=self:check_constraints(new_context, constraint_no+1, constraints, example);
				end
				if match then
					return 1;
				end
			end
		end);
		return match;
	end
end

-- returns the positives and negatives matching examples by a given rule
function _Foil:check_rule(rule, examples, example)
	local covered_positives={};
	local covered_negatives={};
	
	local isMatch=false;
	table.foreachi(examples, function (_, ex)
		local vals=ex.value;
		local bool=ex.bool;
		local context={};
		-- unificates general variables
		table.foreachi(rule:getArguments(), function(i, arg)
			context[arg]=vals[i];
		end);
		if self:check_constraints(context, 1, rule:getConstraints(), example) then
			if bool then
				table.insert(covered_positives, ex);
			else
				table.insert(covered_negatives, ex);
			end
		end
	end);
	return covered_positives, covered_negatives;
end

-- constructor
function Foil(rules_limit, constraints_limit)
	local t=_Foil:clone();
	t.rules_limit=rules_limit;
	t.constraints_limit=constraints_limit;
	return t;
end

-- printers

function print_table(t)
	local first=true;
	table.foreach(t, function (i, v)
		if not first then io.write(", "); end
		first=false;
		io.write(i.."=");
		if v then io.write(v); else io.write("_"); end
	end);
end

function print_example(ex)
	io.write(ex.name.."(");
	print_table(ex.value);
	io.write(")=");print(ex.bool);
end

function print_examples(examples)
	table.foreachi(examples, function (_, ex)
		print_example(ex);
	end);
end

function print_constraints(constraints)
	table.foreachi(constraints, function (i, constraint)
		if i>1 then io.write(", "); end
		print_constraint(constraint);
	end);
	print(".");
end

function print_constraint(constraint, context)
	if constraint:isNegative() then
		io.write("not ");
	end
	io.write(constraint:getName().."(");
	table.foreachi(constraint.args, function (j, arg)
		if j>1 then io.write(", "); end
		if context and context[arg] then
			io.write(context[arg]);
		else
			if context then
				io.write("_");
			else
				io.write(arg);
			end
		end
	end);
	io.write(")");
end

function print_rule(rule)
	io.write(rule:getName().."(");
	table.foreachi(rule:getArguments(), function(i, arg)
		if i>1 then io.write(","); end
		io.write(arg);
	end);
	io.write("):- ");
	print_constraints(rule:getConstraints());
end

function main()
	io.write("example:"); example_name=io.read();
	dofile(example_name..".example");
	rules=Foil(RULES_LIMIT, CONSTRAINTS_LIMIT):process(example);
	table.foreachi(rules, function(_, rule) print_rule(rule); end);
end

main();
