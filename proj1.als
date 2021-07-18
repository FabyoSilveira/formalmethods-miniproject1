
--===============================================
-- DCC831 Formal Methods
-- 2021.1
--
-- Miniproject 1
--
-- Names: Diego Della Rocca de Camargos
--        Fabyo Silveira Amorim
--        Gleison Souza Diniz Mendonca
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
one sig CreatedMessage, Moved, DeletedMessage, Sent, Received, Emptied, CreatedMailbox, DeletedMailbox extends Operator {}

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

------------------------------
-- Frame condition predicates
------------------------------

pred noMailboxChange[mb: Mailbox, t,t': Time] {
    all mailBox: (Mailbox - mb) | mailBox.messages.t' = mailBox.messages.t
    all mailBox: (Mailbox - mb) | mailBox.messages.t'.status = mailBox.messages.t.status

      -- The default mailboxes still in use
     some (InUse.objects.t' & mInbox)
     some (InUse.objects.t' & mDrafts)
     some (InUse.objects.t' & mTrash)
     some (InUse.objects.t' & mSent)

     some (mInbox.status.t' & InUse)
     some (mDrafts.status.t' & InUse)
     some (mTrash.status.t' & InUse)
     some (mSent.status.t' & InUse)

     no (mUserBoxes[t'] & (mInbox + mDrafts + mTrash + mSent))
}

pred noObjectsChangeStatus[ob: Object, t, t': Time] {
    all msg: (Message - ob) | some msg.status.t' => some (msg.status.t' & msg.status.t)
    all msg: (Message - ob) | some msg.status.t  => some (msg.status.t & msg.status.t')

    -- Make all objects live after the transition
    all obj: (InUse.objects.t - ob) | some (InUse.objects.t' & obj)
    all obj: (InUse.objects.t' - ob) | some (InUse.objects.t & obj)
    all obj: (Purged.objects.t - ob) | some (Purged.objects.t' & obj)
    all obj: (Purged.objects.t' - ob) | some (Purged.objects.t & obj)
}

-------------
-- Operators
-------------

pred createMessage [m: Message, t,t': Time] {
  -- Pre-condition
    -- Since this is a fresh message, in terms of the Alloy model, the message
    -- cannot be drawn from the set of messages that are currently active or purged.
    no (m.status.t & ObjectStatus)
    no (m & InUse.objects.t)
    no (m & Purged.objects.t)

    no (m & Mailbox.messages.t)
  -- Post-condition
    -- Create a new message and put it in the drafts mailbox.
    some (m.status.t' & InUse)
    some (m & InUse.objects.t')
    no (m & Purged.objects.t')
    
    some (m & (mDrafts.messages.t'))
    no (mDrafts.messages.t' - (mDrafts.messages.t + m))
    all msg: mDrafts.messages.t | some (msg & mDrafts.messages.t')
    --#(mDrafts.messages.t') = (#(mDrafts.messages.t) + 1)
    -- Frame condition
    noMailboxChange[mDrafts, t, t']
    noObjectsChangeStatus[m, t, t']
    --t' = t.next
    Track.op.t' = CreatedMessage
}

pred getMessage [m: Message, t,t': Time] {
  --Receive a new message in the inbox. In the model, the effect of this operation is
  --simply to add a message coming from outside of the mail app to the inbox. At the time of
  --arrival, the message can be neither active or purged.
  -- Pre-condition
    no (m.status.t & ObjectStatus)
    no (m & InUse.objects.t)
    no (m & Purged.objects.t)

    no (m & Mailbox.messages.t)
  -- Post-condition
    some (m.status.t' & InUse)
    some (m & InUse.objects.t')
    no (m & Purged.objects.t')

    some (m & mInbox.messages.t')
    all msg: (mInbox.messages.t' - m) | some (msg & mInbox.messages.t)
    all msg: (mInbox.messages.t) | some (msg & mInbox.messages.t')
  -- Frame condition
    noMailboxChange[mInbox, t, t']
    noObjectsChangeStatus[m, t, t']
    --t' = t.next
    Track.op.t' = Received
}

pred moveMessage [m: Message, mb': Mailbox, t,t': Time] {
  --Move a given message from its current mailbox to a given, different mailbox.
  -- Pre-condition
    no (mb' & mSent)
    some (m.status.t & InUse)
    some (m & InUse.objects.t)
    no (m & Purged.objects.t)

    some(m & Mailbox.messages.t)
    no (m & mb'.messages.t)
  -- Post-condition
    some (m.status.t' & InUse)
    some (m & InUse.objects.t')
    no (m & Purged.objects.t')

    some (m & mb'.messages.t')
    no (m & (Mailbox - mb').messages.t')
    all msg: m.(~(messages.t)).messages.t' | some (msg & m.(~(messages.t)).messages.t)
    all msg: (m.(~(messages.t)).messages.t - m) | some (msg & m.(~(messages.t)).messages.t')

    all msg: (mb'.messages.t' - m) | some (msg & mb'.messages.t)
    all msg: (mb'.messages.t) | some (msg & mb'.messages.t')
    --no (m & m.(~(messages.t)).messages.t')

    -- Frame condition
    noMailboxChange[(mb' + m.(~(messages.t))), t, t']
    noObjectsChangeStatus[m, t, t']
    --t' = t.next
    Track.op.t' = Moved
}

pred deleteMessage [m: Message, t,t': Time] {
  --Move a given, non yet deleted, message from its current mailbox to the trash mailbox.
  -- Pre-condition
    some (m.status.t & InUse)
    some (m & InUse.objects.t)
    no (m & Purged.objects.t)

    some(m & (Mailbox - mTrash).messages.t)
    no (m & mTrash.messages.t)
  -- Post-condition
    some (m.status.t' & InUse)
    some (m & InUse.objects.t')
    no (m & Purged.objects.t')

    some (m & mTrash.messages.t')
    no (m & (Mailbox - mTrash).messages.t')
    all msg: m.(~(messages.t)).messages.t' | some (msg & m.(~(messages.t)).messages.t)
    all msg: (mTrash.messages.t' - m) | some (msg & mTrash.messages.t)

    all msg: (m.(~(messages.t)).messages.t - m) | some (msg & m.(~(messages.t)).messages.t')
    all msg: mTrash.messages.t | some (msg & mTrash.messages.t')
    --no (m & m.(~(messages.t)).messages.t')

    -- Frame condition
    noMailboxChange[(mTrash + m.(~(messages.t))), t, t']
    noObjectsChangeStatus[m, t, t']

    t' = t.next
    Track.op.t' = DeletedMessage
}

pred sendMessage [m: Message, t,t': Time] {
  --Send a new message. In terms of the Alloy model, the effect of this operation is
  --simply to move a selected message from the draft mailbox to the sent messages mailbox.
  -- Pre-condition
    some (m.status.t & InUse)
    some (m & InUse.objects.t)
    no (m & Purged.objects.t)

    some(m & mDrafts.messages.t)
    no (m & (Mailbox - mDrafts).messages.t)
  -- Post-condition
    some (m.status.t' & InUse)
    some (m & InUse.objects.t')
    no (m & Purged.objects.t')

    some (m & mSent.messages.t')
    no (m & (Mailbox - mSent).messages.t')
    all msg: (mSent.messages.t' - m) | some (msg & mSent.messages.t)
    all msg: (mSent.messages.t) | some (msg & (mSent.messages.t'))

    all msg: (mDrafts.messages.t - m) | some (msg & mDrafts.messages.t') 
    no (m & mDrafts.messages.t')
    all msg: mDrafts.messages.t' | some (msg & mDrafts.messages.t)
  -- Frame condition
    noMailboxChange[(mSent + mDrafts), t, t']
    noObjectsChangeStatus[m, t, t']
    --t' = t.next
    Track.op.t' = Sent
}

pred emptyTrash [t,t': Time] {
  --Permanently purge all messages currently in the trash mailbox.
  -- Pre-condition
  -- Post-condition
    no (Message & mTrash.messages.t')
    all m : Message | (some (m & mTrash.messages.t)) => (some (m.status.t & InUse) and some (m.status.t' & Purged))
    all m : Message | (some (m & mTrash.messages.t)) => (no (m & Purged.objects.t) and
                                                         some (m & InUse.objects.t) and
                                                         some (m & Purged.objects.t') and
                                                         no (m & InUse.objects.t'))

   -- Frame condition
    noMailboxChange[mTrash, t, t']
    --noObjectsChangeStatus[mTrash, t, t']
    all obj: (InUse.objects.t - (Message & mTrash.messages.t)) | some (obj & InUse.objects.t')
    #(InUse.objects.t - (Message & mTrash.messages.t)) = #(InUse.objects.t')

    all obj: (Purged.objects.t' - mTrash.messages.t) | some (obj & Purged.objects.t)

    all obj: (Message & mTrash.messages.t) | no (obj & InUse.objects.t')

    all msg: (Message -  mTrash.messages.t) | some msg.status.t' => some (msg.status.t' & msg.status.t)
    all msg: (Message -  mTrash.messages.t) | some msg.status.t  => some (msg.status.t & msg.status.t')
    --t' = t.next
    Track.op.t' = Emptied
}

pred createMailbox [mb: Mailbox, t,t': Time] {
  --Create a new, empty mailbox and add it to the set of user-created mailboxes.
  -- Define that the mailbox does not exists
  no (mb & (mInbox + mDrafts + mTrash + mSent))
  -- Pre-condition
    no (mb.status.t & ObjectStatus)
    no (mb & InUse.objects.t)
    no (mb & Purged.objects.t)

    no (mb & mUserBoxes[t])
    no mb.messages.t
  -- Post-condition
    some (mb.status.t' & InUse)
    some (mb & InUse.objects.t')
    no (mb & Purged.objects.t')

    some (mb & mUserBoxes[t'])
    no mb.messages.t'
    -- Frame condition
    all mbox: Mailbox | noMailboxChange[mbox, t, t']
    noObjectsChangeStatus[mb, t, t']
    --t' = t.next
    Track.op.t' = CreatedMailbox
}

pred deleteMailbox [mb: Mailbox, t,t': Time] {
  -- Pre-condition
    some (mb.status.t & InUse)
    some (mb & InUse.objects.t)
    no (mb & Purged.objects.t)

    some (mb & mUserBoxes[t])
  -- Post-condition
    some (mb.status.t' & Purged)
    some (mb & Purged.objects.t')
    no (mb & InUse.objects.t')

    no (mb & mUserBoxes[t'])
    all m : Message | (some (m & mb.messages.t)) => (some (m.status.t & InUse) and some (m.status.t' & Purged))
    all m : Message | (some (m & mb.messages.t)) => (no (m & Purged.objects.t) and
                                                     some (m & InUse.objects.t) and
                                                     some (m & Purged.objects.t') and
                                                     no (m & InUse.objects.t'))
  -- Frame condition
   all mBox: (Mailbox - mb) | noMailboxChange[mBox, t, t']
   noObjectsChangeStatus[(mb + mb.messages.t), t, t']
    --t' = t.next
    Track.op.t' = DeletedMailbox
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
  no inbox & (drafts + trash + sent) 
  no drafts & (trash + sent)
  no trash & sent
  -- Just the default mailbox are created
  
  -- The predefined mailboxes are the only active objects
  InUse.objects.t = (mInbox + mDrafts + mTrash + mSent)
  some (mInbox.status.t & InUse)
  some (mDrafts.status.t & InUse)
  some (mTrash.status.t & InUse)
  some (mSent.status.t & InUse)

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


run { System } for 8

--run {  some m: Message | some t: Time | some t2: Time | createMessage[m, t, t2] and System} for 8
--run { some m: Message | some t: Time | some t2: Time | getMessage [m, t, t2] and System} for 8
--run { some m: Message | some mb: Mailbox | some t: Time | some t2: Time | moveMessage [m, mb, t, t2] and System}  for 8
--run { some m: Message | some t: Time | some t2: Time | deleteMessage [m, t, t2] and System} for 8
--run { some m: Message | some t: Time | some t2: Time | (sendMessage [m, t, t2] && (mDrafts != mSent)) and System} for 8
--run { some t: Time | some t2: Time | some (Message & mTrash.messages.t) and emptyTrash [t, t2] and System} for 8
--run { some mb: Mailbox | some t: Time | some t2: Time | createMailbox [mb, t, t2] and System} for 8
--run { some m: Message | some mb: Mailbox | some t: Time | some t2: Time | deleteMailbox [mb, t, t2] and some (m & mb.messages.t) and System} for 8


--------------
-- Properties
--------------

pred p1 {
-- Active mailboxes contain only active messages
 --all mb: Mailbox, t: Time | some (mb & InUse.objects.t) and some (mb.messages.t) => some (mb.messages.t & InUse.objects.t)
 all mb: Mailbox, t: Time | some (mb & InUse.objects.t) and some (mb.messages.t) => mb.messages.t = (InUse.objects.t & mb.messages.t)
} 


pred p2 {
-- Every active message belongs to some active mailbox
 all t: Time, mg: Message | some (mg & InUse.objects.t) => some (messages.t.mg)
}

pred p3 {
-- Mailboxes do not share messages
  all mb1, mb2: Mailbox | (mb1 != mb2) => no (mb1.messages & mb2.messages)
}

pred p4 {
-- The system mailboxes are always active
  all t: Time, smb: (mInbox + mDrafts + mTrash + mSent) | some (smb & (InUse.objects.t))
}

pred p5 {
-- User-created mailboxes are different from the system mailboxes
  all t: Time | no (mUserBoxes[t] & (mInbox + mDrafts + mTrash + mSent))
}

pred p6 {
-- An object can be have Purged status only if it was once active
  all t1: Time | let t2 = t1.next | #Purged.objects.t2  = #(Purged.objects.t2 & (Purged.objects.t1 + InUse.objects.t1))
}


pred p7 {
-- Every sent message was once a draft message
  all t1: Time | let t2 = t1.next | some (mSent.messages.t2) => some (mDrafts.messages.t1 + mSent.messages.t1)
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

--check a1 for 8
--check a2 for 8
--check a3 for 8
--check a4 for 8
--check a5 for 8
--check a6 for 8
--check a7 for 8
