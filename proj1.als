
--===============================================
-- DCC831 Formal Methods
-- 2021.1
--
-- Miniproject 1
--
-- Names: Diego Della Rocca de Camargos
--        Fabyo Silveira Amorim
-- 
--===============================================

--------------
-- Signatures
--------------

open util/ordering[Time] as T
sig Time {}

abstract sig ObjectStatus {}
one sig InUse, Purged extends ObjectStatus {
	objects: Object set -> Time
}

abstract sig Object {
  status: ObjectStatus lone -> Time
}

sig Message extends Object {}

sig Mailbox extends Object {
  messages: Message set -> Time
}

one sig MailApp {
  inbox: Mailbox,
  drafts: Mailbox,
  trash: Mailbox,
  sent: Mailbox,
  userboxes: Mailbox set -> Time
}

abstract sig Operator {}
one sig Created, Moved, Deleted extends Operator {}

one sig Track {
  op: Operator lone -> Time
}


-----------------------
-- Abbreviation macros
-----------------------

-- May be convenient to use

fun mInbox []: Mailbox { MailApp.inbox }
fun mDrafts []: Mailbox { MailApp.drafts }
fun mTrash []: Mailbox { MailApp.trash }
fun mSent []: Mailbox { MailApp.sent }

fun mUserBoxes [t: Time]: set Mailbox { MailApp.userboxes.t }

fun start [] : Time { T/first } -- first instant



-------------
-- Operators
-------------

pred createMessage [m: Message, t,t': Time] {
-- Pre-condition
	-- Since this is a fresh message, in terms of the Alloy model, the message
	-- cannot be drawn from the set of messages that are currently active or purged.
	no (m.status.t & ObjectStatus)
	no (m & Mailbox.messages.t)
-- Post-condition
	-- Create a new message and put it in the drafts mailbox.
	some (m.status.t' & InUse)
	some (m & mDrafts.messages.t')
-- Frame condition

  Track.op.t' = Created
}

pred getMessage [m: Message, t,t': Time] {
-- Pre-condition

-- Post-condition

-- Frame condition

}

pred moveMessage [m: Message, mb': Mailbox, t,t': Time] {
--Move a given message from its current mailbox to a given, different mailbox.
-- Pre-condition
	some (m.status.t & InUse)
	some(m & Mailbox.messages.t)
	no (m & mb'.messages.t)
-- Post-condition
	some (m.status.t' & InUse)
	some (m & mb'.messages.t')
	no (m & m.(~(messages.t)).messages.t')
-- Frame condition

  Track.op.t' = Moved
}

pred deleteMessage [m: Message, t,t': Time] {
--Move a given, non yet deleted, message from its current mailbox to the trash mailbox.
-- Pre-condition
	some (m.status.t & InUse)
	some(m & (Mailbox - mTrash).messages.t)
	no (m & mTrash.messages.t)
-- Post-condition
	some (m.status.t' & InUse)
	some (m & mTrash.messages.t')
	no (m & m.(~(messages.t)).messages.t')
-- Frame condition

  Track.op.t' = Deleted
}

pred sendMessage [m: Message, t,t': Time] {
-- Pre-condition

-- Post-condition

-- Frame condition

}

pred emptyTrash [t,t': Time] {
-- Pre-condition

-- Post-condition

-- Frame condition

}

pred createMailbox [mb: Mailbox, t,t': Time] {
-- Pre-condition

-- Post-condition

-- Frame condition

}

pred deleteMailbox [mb: Mailbox, t,t': Time] {
-- Pre-condition

-- Post-condition

-- Frame condition

}


----------------------------
-- Initial state conditions
----------------------------

pred init [t: Time] {

  -- There are no purged objects at all
	no Purged.objects.t
  -- All mailboxes are empty
	no Mailbox.messages.t
  -- The predefined mailboxes are mutually distinct
	no inbox & (drafts + trash + sent) and 
	no drafts & (trash + sent) and
	no trash & sent
  -- The predefined mailboxes are the only active objects
--	Object & InUse.objects.t = (inbox + drafts + trash + sent)
  -- The app has no user-created mailboxes
	no MailApp.userboxes.t
}


-----------------------
-- Transition relation
-----------------------

pred trans [t,t': Time]  {
  (some mb: Mailbox | createMailbox [mb, t, t'])
  or
  (some mb: Mailbox | deleteMailbox [mb, t, t'])
  or
  (some m: Message | createMessage [m, t, t'])
  or
  (some m: Message | getMessage [m, t, t'])
  or
  (some m: Message | sendMessage [m, t, t'])
  or
  (some m: Message | deleteMessage [m, t, t'])
  or
  (some m: Message | some mb: Mailbox | moveMessage [m, mb, t, t'])
  or
  emptyTrash [t, t']
}



--------------------
-- System predicate
--------------------

-- Denotes all possible executions of the system from a state
-- that satisfies the init condition
pred System {
   init [start]
  all t: Time - T/last | trans [t, T/next[t]]
}


--run { System } for 8
--run { some m: Message | some t: Time | some t2: Time | createMessage[m, t, t2] }
--run { some m: Message | some mb: Mailbox | some t: Time | some t2: Time | moveMessage [m, mb, t, t2] }  
run { some m: Message | some t: Time | some t2: Time | deleteMessage [m, t, t2] } 

--------------
-- Properties
--------------

pred p1 {
-- Active mailboxes contain only active messages

}

pred p2 {
-- Every active message belongs to some active mailbox

}

pred p3 {
-- Mailboxes do not share messages

}

pred p4 {
-- The system mailboxes are always active

}

pred p5 {
-- User-created mailboxes are different from the system mailboxes

}

pred p6 {
-- An object can be have Purged status only if it was once active

}


pred p7 {
-- Every sent message was once a draft message

}

--------------
-- Assertions
--------------

assert a1 { System => p1 }
assert a2 { System => p2 }
assert a3 { System => p3 }
assert a4 { System => p4 }
assert a5 { System => p5 }
assert a6 { System => p6 }
assert a7 { System => p7 }
