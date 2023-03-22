//#title Host protocol
//#desc Define the host state machine here: message type, state machine for executing one
//#desc host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.t.dfy"
//#extract network.t.template solution network.t.dfy

module Host {
  import opened UtilitiesLibrary
  import opened HostIdentifiers
  import Network

  // Define your Message datatype here.
  datatype Message =
/*{*/
  | GrantMsg(dest: HostId, epoch: nat)
/*}*/

  // Define your Host protocol state machine here.
  datatype Constants = Constants(numHosts: nat, myId:HostId) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    predicate Configure(numHosts: nat, id:HostId) {
      && this.numHosts == numHosts
      && this.myId == id
    }
  }

  datatype Variables = Variables(
/*{*/
    // are we the lock holder?
    holder: bool,
    // highest epoch number witnessed by this node so far
    epoch: nat
/*}*/
  )

  predicate Init(c:Constants, v:Variables) {
/*{*/
  if c.myId == 0 then
    (&& v.holder == true
     && v.epoch == 1)
  else
    (&& v.holder == false
    && v.epoch == 0)
/*}*/
  }

/*{*/
  predicate SendGrant(c:Constants, v:Variables, v':Variables, dest: HostId,
    msgOps: Network.MessageOps<Message>)
  {
    // "enabling"
    && msgOps.recv == None
    && v.holder == true
    // transition
    && msgOps.send == Some(GrantMsg(dest, v.epoch + 1))
    && v' == v.(holder := false)
  }

  predicate RecvGrant(c:Constants, v:Variables, v':Variables,
    msgOps: Network.MessageOps<Message>)
  {
    // "enabling"
    && msgOps.recv.Some? && msgOps.recv.value.GrantMsg?
    && var dest := msgOps.recv.value.dest;
       var msgEpoch := msgOps.recv.value.epoch;
    // only receive grant messages that were sent to this host
    && dest == c.myId
    // only accept messages with epoch numbers that are valid
    && msgEpoch > v.epoch
    // transition
    && v' == v.(holder := true).(epoch := msgEpoch)
    && msgOps.send == None
  }
/*}*/
  // JayNF
  datatype Step =
/*{*/
    | SendGrantStep(dest: HostId)
    | RecvGrantStep
/*}*/

  predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
/*{*/
  case SendGrantStep(dest) => SendGrant(c, v, v', dest, msgOps)
  case RecvGrantStep => RecvGrant(c, v, v', msgOps)
/*}*/
  }

  predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
