-- Murphi Model of a Simplified Version of TokenB Token Coherence
-- Alan J. Hu, 2014-Oct-2

-- Note:  I have deliberately inserted two bugs.  There may be others!

-- Try these tasks, in roughly this order:
-- 1.  Run Murphi on this model.  It will show you an error trace to the
--     first bug.  You should practice reading the error trace.
-- 2.  If you search in the text for "OBVIOUS BUG" you will see the bug,
--     along with the correction.  Fix the bug and re-run Murphi.
--     Now, you will see it run reachability to completion, indicating
--     no more bugs.  Yay!  But wait... I said there were TWO bugs...
-- 3.  To find the second bug, you will need to add additional properties
--     to check, at the end of the file.  To figure out good properties,
--     you'll want to read the Token Coherence paper and think about things
--     to check.  You may find other bugs beyond the one I planted.
-- 4.  While you are doing steps 2 and 3, you'll see that you are exploring
--     a lot of states.  You should try reducing the state count by introducing
--     Scalarset types where appropriate.
-- 5.  Similar to step 4, there is additional state savings that can be
--     achieved by using UNDEFINED and Undefine to erase the information
--     in variables that are no longer storing useful data.  How small
--     can you shrink the reachable state count?  With the Const scaling
--     parameters at the values I gave you (ProcCount=2, AddressCount=1,
--     ValueCount=2, TokensPerAddress=2, and BufferDepth=3), I got this
--     down to 238240 states with the 2nd bug, or 128187 states after
--     the second bug was fixed.  Can you do better?
-- 6.  Finally, if you are getting good state savings, you can try scaling
--     the model up a bit, e.g., try 3 processors, or a buffer depth of 4.
--     How big can you scale the parameters?  Does it make sense to scale
--     the AddressCount parameter?

Const
  ProcCount: 2;
  AddressCount: 1;
  ValueCount: 2;
  TokensPerAddress: 2;
  BufferDepth: 3;

Type
  val_t: 0..99;
  Pid: 0..ProcCount-1;  -- Processor ID
  Address: 0..AddressCount-1;
  Value: 0..ValueCount-1;
  TokenCounter: 0..TokensPerAddress;
  MsgNum: 0..BufferDepth-1;

  -- The different kinds of messages that can be sent.
  -- TokensOnly is for tokens without valid data.
  -- TokensData also contains a value for the data.
  MessageType: Enum{ReqS,ReqM,TokensOnly,TokensData};

  -- The format for a message.
  NetMessage: Record
		msg_type: MessageType;
		from: Pid;
		tokens: TokenCounter;
		owner: Boolean;
		a: Address;
		d: Value;
	      End;

  -- This declares a network to be an unordered collection of 
  -- of messages, with maximum size BufferDepth.
  Network: MultiSet[BufferDepth] of NetMessage;

  ProcState: Record
	      -- I used to have additional state here, hence the record.

	      cache: Array[Address] of
			Record
			  state: Enum{Modified, Owned, Shared, Invalid};
			  -- This MOSI state is not actually needed, as
			  -- the number of tokens mostly determines the state.
			  -- (See the paper, p. 113, column 1, 2nd paragraph.)
			  -- However, these states are convenient to have,
			  -- and I do need some way to tell whether v has
			  -- the correct value yet, since I might receive
			  -- tokens without valid data before I get a token
			  -- with the actual data value.
			  -- I will encode this as remaining in state Invalid
			  -- until a TokensData message arrives.
			  v: Value;
			  tokens: TokenCounter;
			End;
	      -- In order to avoid modeling a real cache,
	      -- I'm allowing each processor to cache all address lines.
	    End;

  MemState: Array[Address] of
		Record
		  tokens: TokenCounter;
		  owner: Boolean;
		  v: Value;
		End;

Var
  -- Out-of-order network of messages to processors
  toCaches: Array[Pid] of MultiSet[BufferDepth] of NetMessage;
  toMem: MultiSet[BufferDepth] of NetMessage; -- network to memory
  procs: Array[Pid] of ProcState;
  mem: MemState;


-- Network Functions

-- Function to count the number of tokens in transit for a given address
--Function CountTokensInTransit(input: Address): TokenCounter;
--Var
--  tokensInTransit: TokenCounter;  -- Variable to store tokens in transit
--  p: Pid;                                -- Loop variable for processor
--  two_token:TokenCounter;
--Begin
--  tokensInTransit := 0;  -- Initialize the counter
--  two_token := 0 ;
--    two_token := MultisetCount(i:toMem, toMem[i].tokens = 2);
  

  -- Iterate over the processors
  --For p := 0 to ProcCount-1 Do
    -- Use MultisetCount to iterate through valid messages in the toCaches multiset
    --tokensInTransit := tokensInTransit + 
    --                   MultisetCount(i: toCaches[p], toCaches[p][i].a = a);
  --Endfor;

--  Return two_token;
--End;


Procedure SendCache(m: MessageType; toProc: Pid; fromProc: Pid;
		    tokens: TokenCounter; owner: Boolean; a: Address; d: Value);
Var msg: NetMessage;
Begin
  msg.msg_type := m;
  msg.from := fromProc;
  msg.tokens := tokens;
  msg.owner := owner;
  msg.a := a;
  msg. d := d;
  MultiSetAdd(msg,toCaches[toProc]);
End;

Procedure SendMem(m: MessageType; from: Pid; tokens: TokenCounter;
			owner: Boolean; a: Address; d: Value);
Var msg: NetMessage;
Begin
  msg.msg_type := m;
  msg.from := from;
  msg.tokens := tokens;
  msg.owner := owner;
  msg.a := a;
  msg. d := d;
  MultiSetAdd(msg,toMem);
End;

Procedure Broadcast(m: MessageType; from: Pid; tokens: TokenCounter;
			owner: Boolean; a: Address; d: Value);
Begin
  for toProc: Pid do
    if (toProc != from) then
      SendCache(m,toProc,from,tokens,owner,a,d);
    endif;
  endfor;
  SendMem(m,from,tokens,owner,a,d);
End;


--------------------
-- Rules
--------------------

-- Each processor can decide to:
--     Request a read-only copy of an address it doesn't have (ReqS)
--     Request a writable copy of an address it doesn't have (ReqM)
--     Write back any address it has writable
--     Throw away any address it has shared
--     Change the value of any exclusive copy it has
-- Note that you want to model this so that only one transaction happens at
-- a time.  For example, don't allow the processor to atomically write back
-- it's entire cache.  The only "exception" (sort of) is that the protocol
-- allows sending multiple messages, e.g. sending an invalidate to all
-- processors who have an address cached.

-- Here are some hints:

-- A rule can have a title.  This makes error traces easier to read.

-- You can enclose rules in rulesets, which create a copy of a rule for
-- each value of a type.  For example:
-- Ruleset p: Pid Do
--   Rule "Foo 1"
--     ...
--   Endrule;
--   Rule "Foo 2"
--     ...
--   Endrule;
--     etc.
-- Endruleset;
-- This creates copies of the rule for each possible processor p.

-- Another handy construct is the Alias command.  For example
-- Alias me: procs[p] Do
--   ...
-- Endalias;
-- Everywhere within the Alias statement, the identifier me becomes
-- shorthand for procs[p].  This saves a lot of typing.

Ruleset p: Pid Do
  Ruleset a: Address Do

    Rule "Request Shared"
      (procs[p].cache[a].state = Invalid) &
      -- Make sure enough room in network for request
      (Forall p1: Pid Do
	(MultisetCount(i: toCaches[p1], TRUE) < BufferDepth)
       Endforall) &
      (MultisetCount(i: toMem, TRUE) < BufferDepth)
    ==>
      Broadcast(ReqS, p, 0, False, a, 0);
      -- Notice how I used UNDEFINED here, since the message doesn't
      -- need to contain tokens or a value.  Leaving these undefined
      -- results in a smaller set of reachable states (since the
      -- verifier doesn't explore states with different values of these.
    Endrule;

    Rule "Request Exclusive"
      (procs[p].cache[a].state != Modified) &
      -- Make sure enough room in network for request
      (Forall p1: Pid Do
	(MultisetCount(i: toCaches[p1], TRUE) < BufferDepth)
       Endforall) &
      (MultisetCount(i: toMem, TRUE) < BufferDepth)
    ==>
      Broadcast(ReqM, p, 0, False, a, 0);
    Endrule;

    Rule "Evict Clean Cache Line"
      (procs[p].cache[a].state = Shared) &
      (MultisetCount(i: toMem, TRUE) < BufferDepth)
    ==>
      procs[p].cache[a].state := Invalid;
      SendMem(TokensOnly, 0, procs[p].cache[a].tokens, False, a, 0);
      procs[p].cache[a].tokens := 0;
    Endrule;

    Rule "Evict Owned or Modified Cache Line"
      ((procs[p].cache[a].state = Owned) | (procs[p].cache[a].state = Modified)) &
      (MultisetCount(i: toMem, TRUE) < BufferDepth)
    ==>
      Alias me: procs[p].cache[a] Do
        me.state := Invalid;
        SendMem(TokensData, 0, me.tokens, True, a, me.v);
        me.tokens := 0;
      Endalias;
    Endrule;

    Ruleset v: Value Do
      Rule "Write to Dirty Data"
	-- ***** OBVIOUS BUG *****
        -- (procs[p].cache[a].state = Shared)	-- This line is wrong.
         (procs[p].cache[a].state = Modified)	-- This is what it should be.
      ==>
	procs[p].cache[a].v := v;
      Endrule;
      Rule "Write to Clean Data"
	-- If I have all tokens, I can modify the data.
	(procs[p].cache[a].state != Modified) &
        (procs[p].cache[a].tokens = TokensPerAddress)
      ==>
	procs[p].cache[a].state := Modified;
	procs[p].cache[a].v := v;
      Endrule;
    Endruleset;

  Endruleset;
Endruleset;


-- For the network, it's easiest to get a valid message from the multiset
-- using the Choose command, and then do whatever action is needed to
-- process that message.  In our protocol, we have a separate channel
-- to each cache, as well as one to memory.

-- You use Choose sort of like Alias or Ruleset.  For example:
-- Choose i: upchannel Do
--   ...
-- Endchose;
-- allows you to refer to upchannel[i], within the scope of the Choose
-- statement, to get an arbitrary message in upchannel.
-- You can use the Send procedures I've given you to see how to add
-- things to multisets.  To remove them, use the MultiSetRemove statement.
-- For example, the following chooses an arbitrary message from upchannel
-- and deletes it.
-- Choose i: upchannel Do
--   Rule "Delete a random message"
--     True -- This rule is always enabled
--   ==>
--     MultiSetRemove(i, upchannel);
--   Endrule;
-- Endchoose;

-- Note that there appears to be a Murphi bug relating Choose and Alias.
-- If you get weird error messages when using an Alias within a Choose,
-- try moving the Alias to within the action part of the rule:
-- Choose i: upchannel Do
--   Rule "Delete a random message"
--     True -- This rule is always enabled
--   ==>
--     Alias foobar: upchannel Do
--       MultiSetRemove(i, foobar);
--     Endalias;
--   Endrule;
-- Endchoose;

Ruleset p: Pid Do
  Choose i: toCaches[p] Do
    Alias msg: toCaches[p][i] Do

      Rule "Processor gets ReqS"
        (msg.msg_type = ReqS) &
	(MultisetCount(i: toCaches[msg.from], TRUE) < BufferDepth)
      ==>
	Alias mycache: procs[p].cache[msg.a] Do
        if mycache.tokens > 0 then
	        if (mycache.state = Modified) | (mycache.state = Owned) then
	            if mycache.tokens = 1 then
	                SendCache(TokensData, msg.from, 0, 1, True, msg.a, mycache.v);
                    mycache.tokens := mycache.tokens - 1;
                    mycache.state := Invalid;
                else
                    SendCache(TokensData, msg.from, 0, 1, False, msg.a, mycache.v);
                    mycache.tokens := mycache.tokens - 1;
                    mycache.state := Owned;
	            endif;
	        endif;
        endif;
	Endalias;
        MultisetRemove(i, toCaches[p]);
      Endrule;

      Rule "Processor gets ReqM"
        (msg.msg_type = ReqM) &
	(MultisetCount(i: toCaches[msg.from], TRUE) < BufferDepth)
      ==>
	Alias mycache: procs[p].cache[msg.a] Do
          if mycache.tokens > 0 then
	    if (mycache.state = Modified) | (mycache.state = Owned) then
	      SendCache(TokensData, msg.from, 0, mycache.tokens, True, msg.a, mycache.v);
	    else
	      SendCache(TokensOnly, msg.from, 0, mycache.tokens, False, msg.a, 0);
	    endif;
	    mycache.tokens := 0;
	    mycache.state := Invalid;
	     mycache.v := 0;
          endif;
	Endalias;
        MultisetRemove(i, toCaches[p]);
      Endrule;

      Rule "Processor gets Tokens without Data"
        msg.msg_type = TokensOnly
      ==>
	Alias mycache: procs[p].cache[msg.a] Do
          mycache.tokens := mycache.tokens + msg.tokens;
          if mycache.tokens = TokensPerAddress then
            mycache.state := Modified;
        endif;
          if msg.owner & mycache.tokens > 0 & mycache.tokens < TokensPerAddress then
	        mycache.state := Owned;
          endif;
          if !msg.owner & mycache.tokens > 0 & mycache.tokens < TokensPerAddress then
            mycache.state := Shared;
          endif;
          if mycache.tokens = 0 then
            mycache.state := Invalid;
          endif;
	Endalias;
        MultisetRemove(i, toCaches[p]);
      Endrule;

      Rule "Processor gets Tokens with Data"
        msg.msg_type = TokensData
      ==>
	Alias mycache: procs[p].cache[msg.a] Do
          mycache.tokens := mycache.tokens + msg.tokens;
	  mycache.v := msg.d;
          if mycache.tokens = TokensPerAddress then
            mycache.state := Modified;
        endif;
          if msg.owner & mycache.tokens > 0 & mycache.tokens < TokensPerAddress then
	        mycache.state := Owned;
          endif;
          if !msg.owner & mycache.tokens > 0 & mycache.tokens < TokensPerAddress then
            mycache.state := Shared;
          endif;
          if mycache.tokens = 0  then
            mycache.state := Invalid;
          endif;
	Endalias;
        MultisetRemove(i, toCaches[p]);
      Endrule;

    Endalias;
  Endchoose;
Endruleset;

Choose i: toMem Do
  Alias msg: toMem[i] Do

    Rule "Memory gets ReqS"
      (msg.msg_type = ReqS) &
      (MultisetCount(i: toCaches[msg.from], TRUE) < BufferDepth)
    ==>
      if mem[msg.a].owner then
        -- This is only my problem if I'm the owner.
        if mem[msg.a].tokens > 1 then
	  -- Send data, but retain ownership.
	  SendCache(TokensData, msg.from, 0, 1, False, msg.a, mem[msg.a].v);
	  mem[msg.a].tokens := mem[msg.a].tokens - 1;
	elsif mem[msg.a].tokens = 1 then
	  -- My last token.  Send data as well as ownership.
	  SendCache(TokensData, msg.from, 0, 1, True, msg.a, mem[msg.a].v);
	  mem[msg.a].tokens := mem[msg.a].tokens - 1;
	  mem[msg.a].owner := False;
        endif;
      endif;
      MultisetRemove(i, toMem);
    Endrule;

    Rule "Memory gets ReqM"
      (msg.msg_type = ReqM) &
      (MultisetCount(i: toCaches[msg.from], TRUE) < BufferDepth)
    ==>
      if mem[msg.a].tokens > 0 then
	if mem[msg.a].owner then
	  SendCache(TokensData, msg.from, 0, mem[msg.a].tokens, True, msg.a, mem[msg.a].v);
	else
	  SendCache(TokensOnly, msg.from, 0, mem[msg.a].tokens, False, msg.a, 0);
	endif;
	mem[msg.a].tokens := 0;
	mem[msg.a].owner := False;
	 mem[msg.a].v := 0;
      endif;
      MultisetRemove(i, toMem);
    Endrule;

    Rule "Memory gets Tokens without Data"
      msg.msg_type = TokensOnly
    ==>
      mem[msg.a].tokens := mem[msg.a].tokens + msg.tokens;
      MultisetRemove(i, toMem);
    Endrule;

    Rule "Memory gets Tokens with Data"
      msg.msg_type = TokensData
    ==>
      mem[msg.a].tokens := mem[msg.a].tokens + msg.tokens;
      mem[msg.a].v := msg.d;
      if msg.owner then
	mem[msg.a].owner := True;
      endif;
      MultisetRemove(i, toMem);
    Endrule;

  Endalias;
Endchoose;

-- This defines the start states
Ruleset v: Value Do
Startstate

  -- Processors start out with empty caches
  For p: Pid Do
    For a: Address Do
      procs[p].cache[a].state := Invalid;
    procs[p].cache[a].v := 0;
      procs[p].cache[a].tokens := 0;
    Endfor;
  Endfor;

  -- Memory starts out with an arbitrary value in all locations
  For a: Address Do
    mem[a].tokens := TokensPerAddress;
    mem[a].owner := True;
    mem[a].v := v;
  Endfor;

  -- Network starts out empty.
  Undefine toCaches;
  Undefine toMem;

Endstartstate;
Endruleset;


--------------------
-- Specification
--------------------
-- Here's an example property to check.  You can (and should) put down
-- additional specs here as well.  Just use the Invariant statement to
-- add other properties to check.

-- Also, it's often handy to use Assert statements within the rules
-- to check that the model is behaving as you expect.

-- Shared entries must agree with each other.
    Invariant "Shared entries must agree"
      Forall a: Address Do
	Forall p1: Pid; p2: Pid Do
	  ((procs[p1].cache[a].state = Shared)
	  & (procs[p2].cache[a].state = Shared))
	  -> (procs[p1].cache[a].v = procs[p2].cache[a].v)
	Endforall
      Endforall;


    Invariant "Conservation of tokens"
        Forall a: Address Do
            MultisetCount(i: toCaches[0], TRUE) = 0 & MultisetCount(i: toCaches[1], TRUE) = 0 & MultisetCount(i: toMem, TRUE) = 0
            ->
              mem[a].tokens + procs[0].cache[a].tokens + procs[1].cache[a].tokens = TokensPerAddress
        Endforall;

    Invariant "A processor can write a block only if it holds all T tokens for that block."
       Forall a: Address Do
            (procs[0].cache[a].tokens = TokensPerAddress & mem[a].owner = False) | (procs[1].cache[a].tokens = TokensPerAddress & mem[a].owner = False)
           -> procs[0].cache[a].state = Modified | procs[1].cache[a].state = Modified | procs[0].cache[a].state = Owned | procs[1].cache[a].state = Owned
        Endforall;

    Invariant "A processor can read a block only if it holds at least one token for that block and has valid data."
        -- Also means, if it has 0 tokens, then the only state it can be is Invalid
        Forall a: Address Do
            procs[0].cache[a].tokens = 0 | procs[1].cache[a].tokens = 0
            -> procs[0].cache[a].state = Invalid | procs[1].cache[a].state = Invalid
        Endforall;

    --Invariant "The cache in the Owned state must have 1 to T-1 tokens and the memory must not be the owner (p0)"
    --    Forall a: Address Do
    --        procs[0].cache[a].state = Owned
    --        -> mem[a].owner = False & procs[0].cache[a].tokens > 0 & procs[0].cache[a].tokens < TokensPerAddress
    --    Endforall;

    --Invariant "The cache in the Owned state must have 1 to T-1 tokens and the memory must not be the owner (p1)"
    --    Forall a: Address Do
    --        procs[1].cache[a].state = Owned
    --        -> mem[a].owner = False & procs[1].cache[a].tokens > 0 & procs[1].cache[a].tokens < TokensPerAddress
    --    Endforall;

    --Invariant "The cache in the Shared state must have 1 to T-1 tokens (p0)"
    --    Forall a: Address Do
    --        procs[0].cache[a].state = Shared
    --        -> procs[0].cache[a].tokens > 0 & procs[0].cache[a].tokens < TokensPerAddress
    --    Endforall;

    --Invariant "The cache in the Shared state must have 1 to T-1 tokens (p1)"
    --    Forall a: Address Do
    --        procs[1].cache[a].state = Shared
    --        -> procs[1].cache[a].tokens > 0 & procs[1].cache[a].tokens < TokensPerAddress
    --    Endforall;

    --Invariant "The cache in the Invalid state must have 0 tokens (p0)"
    --    Forall a: Address Do
    --        procs[0].cache[a].state = Invalid
    --        -> procs[0].cache[a].tokens = 0
    --    Endforall;
    
    --Invariant "The cache in the Invalid state must have 0 tokens (p1)"
    --    Forall a: Address Do
    --        procs[1].cache[a].state = Invalid
    --        -> procs[1].cache[a].tokens = 0
    --    Endforall;


        
        


    



