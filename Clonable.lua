_Clonable={};

function _Clonable:doClone(obj, initial, reftab)
	local new=initial;
	local i,v;
	for i,v in obj do
		if type(v) == "table" then
			if v._unique then
				-- recursive reference
				new[i]=reftab[v._unique];
			else
				v._unique=reftab._unique;
				reftab[v._unique]=v;
				reftab._unique=reftab._unique+1;
				new[i]=self:doClone(v, {}, reftab);
			end
		else
			new[i]=v;
		end
	end
	return new;
end

function _Clonable:doClean2(obj)
	local i,v;
	obj._unique=nil;
	for i,v in obj do
		if type(v) == "table" then
			self:doClean(v);
		end
	end
end

function _Clonable:doClean(obj, reftab)
	table.foreach(reftab, function(i, v)
		if type(v) == "table" then
			v._unique=nil;
		end
	end);
end

function _Clonable:clone()
	local reftab={ _unique=1 };
	local t=self:doClone(self, {}, reftab);
	self:doClean(t, reftab);
	return t;
end

function _Clonable:cloneTo(target)
	local reftab={ _unique=1 };
	reftab[1]=self;
	local t=self:doClone(self, target or {}, reftab);
	self:doClean(t, reftab);
	return t;
end

function Clonable(atts)
	local t=atts or {};
	local i,v;
	for i,v in _Clonable do
		t[i]=v;
	end
	return t;
end
