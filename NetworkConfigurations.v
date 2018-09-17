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

Definition firewall_config R := network_topology R -> flow -> bool.

Definition nonexistent_firewall : firewall_config ipAddress :=
  (fun _ _ => true).
