module KeySchedule

// cwinter: this file should be removed, but Epochs.fst still depends on these remaining definitions.

open FStar.Bytes

open TLSInfo

type ms = FStar.Bytes.bytes
type pms = FStar.Bytes.bytes
type ems #li (i:exportId li) = Hashing.Spec.tag (exportId_hash i)

type recordInstance =
  | StAEInstance: #id:TLSInfo.id -> StAE.reader (peerId id) -> StAE.writer id -> recordInstance

type exportKey = (li:logInfo & i:exportId li & ems i)
