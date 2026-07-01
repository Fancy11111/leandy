import Mathlib.Tactic
import Leandy.Macros.AesopRuleSets

macro "aesop_type_system" : tactic =>
  `(tactic| aesop (rule_sets := [type_system, split_cf, protocol]) (config := {useDefaultSimpSet := false}))
macro "aesop_type_system?" : tactic =>
  `(tactic| aesop? (rule_sets := [type_system, split_cf, protocol]) (config := {useDefaultSimpSet := false}))

macro "aesop_type_system!" : tactic =>
  `(tactic| aesop (rule_sets := [type_system, type_system_forward, split_cf, protocol]) (config := {useDefaultSimpSet := false}))
macro "aesop_type_system!?" : tactic =>
  `(tactic| aesop? (rule_sets := [type_system, type_system_forward, split_cf, protocol]) (config := {useDefaultSimpSet := false}))

add_aesop_rules (rule_sets := [split_cf]) norm autoParam

attribute [aesop (rule_sets := [split_cf]) norm]
  List.not_mem_nil List.mem_cons
