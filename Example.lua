_Example=Clonable();

function _Example:add(name, value, bool)
	self.arity[name]=self.arity[name] or 0;
	if self.arity[name]<table.getn(value) then
		self.arity[name]=table.getn(value);
	end
	table.insert(self.examples, {name=name, value=value, bool=bool});
	local isAdded=false;
	table.foreachi(self.predicates, function(_, p)
		if p==name then
			isAdded=true;
			return 1;
		end
	end);
	if not isAdded then
		table.insert(self.predicates, name);
	end
end

function _Example:getArity(name)
	return self.arity[name];
end

function _Example:getTargetArity()
	return self.arity[self:getTargetAttribute()];
end

function _Example:getTargetAttribute()
	return self.target_attribute;
end

function _Example:getPredicates()
	return self.predicates;
end

function _Example:getTargetExamples()
	return self:getExamples(self:getTargetAttribute());
end

function _Example:getExamples(predicate_name)
	local examps={};
	table.foreach(self.examples, function(_, example)
		if example.name==predicate_name then
			table.insert(examps, example);
		end
	end);
	return examps;
end

function _Example:splitExamples()
	local pos={};
	local neg={};
	table.foreach(self.examples, function(_, example)
		if example.name==self.target_attribute then
			if example.bool then	
				table.insert(pos, example);
			else
				table.insert(neg, example);
			end
		end
	end);
	return pos, neg;
end

function Example(target_attribute)
	local t=_Example:clone();
	t.target_attribute=target_attribute;
	t.examples={};
	t.predicates={};
	t.arity={};
	return t;
end
