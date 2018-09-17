(* TODO: add bounds for port in [0, 65535) *)
Definition port := nat.

(* TODO: add bounds for IP components in [0, 256) *)
(* TODO: support IPv6 addresses? *)
Definition ipAddress : Set := (nat * nat * nat * nat).

(* TODO: support more interesting protocol info here *)
Definition protocol := unit.

Record flow := {
  SrcIp : ipAddress;
  SrcPort : port;
  DestIp : ipAddress;
  DestPort : port;
  Protocol : protocol
}.

Definition network_topology (Router : Set) := Router -> Router -> bool.

Definition network_policy R := network_topology R -> flow -> bool.

Definition everything_allowed_policy : network_policy ipAddress :=
  (fun _ _ => true).
