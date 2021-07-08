
--===============================================
-- DCC831 Formal Methods
-- 2021.1
--
-- Miniproject 1
--
-- Name:  <replace with your name>
--
--===============================================

--------------
-- Signatures
--------------

open util/ordering[Time] as T
sig Time {}

abstract sig ObjectStatus {}
one sig InUse, Purged extends ObjectStatus {}

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

}

pred getMessage [m: Message, t,t': Time] {

}

pred moveMessage [m: Message, mb': Mailbox, t,t': Time] {

}

pred deleteMessage [m: Message, t,t': Time] {

}

pred sendMessage [m: Message, t,t': Time] {

}

pred emptyTrash [t,t': Time] {

}

pred createMailbox [mb: Mailbox, t,t': Time] {

}

pred deleteMailbox [mb: Mailbox, t,t': Time] {

}


----------------------------
-- Initial state conditions
----------------------------

pred init [t: Time] {
  -- There are no purged objects at all

  -- All mailboxes are empty

  -- The predefined mailboxes are mutually distinct

  -- The predefined mailboxes are the only active objects

  -- The app has no user-created mailboxes

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


run { System } for 8


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
