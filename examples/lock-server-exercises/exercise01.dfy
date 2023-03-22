//#title Midterm Project
//#desc Build a distributed lock server. Define how a host implements your
//#desc protocol in host.v.dfy; write your safety spec and proof here.

// This challenge differs from LockServer (from chapters 03 and 04) in two
// ways. First, there is no central server that coordinates the activity.
// Second, the hosts can communicate only via asynchronous messages; a single
// state machine transition cannot simultaneously read or update the state of
// two hosts.
//
// To guard against duplicate messages, the nodes associate a monotonically
// increasing epoch number with the lock. Initially, node 0 holds the lock and
// its epoch number is 1, while all other nodes with an epoch of 0 (and not
// holding the lock). A node that holds the lock can “grant” it to another
// node by sending them a “Grant” message which has an epoch number that is
// greater than the node's epoch number. A node that receives such a message
// will become the new holder and will set its epoch number to the message’s
// epoch number.

// You'll first need to modify 'host.v.dfy' to define the protocol message
// format and the host behavior.
// Then come back here define the safety condition and prove that the
// distributed system made from that protocol maintains it.

include "distributed_system.t.dfy"
//#extract distributed_system.t.template solution distributed_system.t.dfy

module SafetySpec {
  import opened HostIdentifiers
  import DistributedSystem

  // Define this predicate to be true if idx is a valid host ID and that host's
  // Variables indicates that it holds the lock.
  predicate HostHoldsLock(c:DistributedSystem.Constants, v:DistributedSystem.Variables, idx: int) {
    && v.WF(c)
/*{*/
    && c.ValidHostId(idx)
    && v.hosts[idx].holder
/*}*/
  }

  // No two hosts think they hold the lock simulatneously.
  predicate Safety(c:DistributedSystem.Constants, v:DistributedSystem.Variables) {
/*{*/
    forall idx1: HostId, idx2: HostId ::
    HostHoldsLock(c, v, idx1) && HostHoldsLock(c, v, idx2) ==>
    idx1 == idx2
/*}*/
  }
}

module Proof {
  import opened HostIdentifiers
  import Host
  import opened DistributedSystem
  import opened SafetySpec

  // Here's a predicate that will be very useful in constructing inviariant conjuncts.
  predicate InFlight(c:Constants, v:Variables, message:Host.Message) {
    && v.WF(c)
    && message in v.network.sentMsgs
/*{*/
    && c.ValidHostId(message.dest)
    && message.epoch > v.hosts[message.dest].epoch
/*}*/
  }

/*{*/
  predicate InFlightGrantImpliesNoLockHolder(c: Constants, v: Variables)
  requires v.WF(c)
  {
    forall message: Host.Message ::
    InFlight(c, v, message) ==>
    forall idx: HostId | c.ValidHostId(idx) ::
    !v.hosts[idx].holder
  }

  predicate LockHolderHasHighestEpoch(c: Constants, v: Variables)
  requires v.WF(c)
  {
    // idx is lock holder
    forall idx: HostId | c.ValidHostId(idx) && v.hosts[idx].holder ::
    forall idx': HostId | c.ValidHostId(idx') && idx' != idx ::
    // lock holder's epoch number is higher than any other node's
    v.hosts[idx].epoch > v.hosts[idx'].epoch
  }

  predicate InFlightGrantHasHighestEpoch(c: Constants, v: Variables)
  requires v.WF(c)
  {
    forall msg: Host.Message | InFlight(c, v, msg) ::
    forall idx: HostId | c.ValidHostId(idx) ::
    msg.epoch > v.hosts[idx].epoch
  }

  predicate NoTwoInFlightGrants(c: Constants, v: Variables)
  requires v.WF(c)
  {
    forall msg1: Host.Message, msg2: Host.Message |
      InFlight(c, v, msg1) && InFlight(c, v, msg2) ::
      msg1 == msg2
  }
/*}*/

  predicate Inv(c: Constants, v:Variables) {
/*{*/
    && v.WF(c)
    && InFlightGrantImpliesNoLockHolder(c, v)
    && LockHolderHasHighestEpoch(c, v)
    && InFlightGrantHasHighestEpoch(c, v)
    && NoTwoInFlightGrants(c, v)
    && Safety(c, v)
/*}*/
  }

  lemma SafetyProof(c: Constants, v:Variables, v':Variables)
    ensures Init(c, v) ==> Inv(c, v)
    ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
    ensures Inv(c, v) ==> Safety(c, v)
  {
    // Develop any necessary proof here.
/*{*/
    assert Init(c, v) ==> Inv(c, v);
    assert Inv(c, v) ==> Safety(c, v);
    if Inv(c, v) && Next(c, v, v') {
      assert v'.WF(c);
      var id : HostId, msgOps: Network.MessageOps<Host.Message> :|
        NextStep(c, v, v', Step(id, msgOps));
      var step :| Host.NextStep(c.hosts[id], v.hosts[id], v'.hosts[id], msgOps, step);
      match step
        case SendGrantStep(dest: HostId) => {
          var msg := msgOps.send.value;
          if c.ValidHostId(msg.dest) {
            assert InFlight(c, v', msg);
          }
          assert Inv(c, v');
        }
        case RecvGrantStep => {
          var msg := msgOps.recv.value;
          assert InFlight(c, v, msg);
          assert !v.hosts[id].holder;
          // assert LockHolderHasHighestEpoch(c, v');
          assert !InFlight(c, v', msg);
          assert forall msg': Host.Message ::
            !InFlight(c, v, msg') ==> !InFlight(c, v', msg');
          assert NoTwoInFlightGrants(c, v');
        }
      assert Inv(c, v');
    }
/*}*/
  }
}
