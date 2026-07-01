instance Subtype.instRepr {P: α → Prop} [inst: Repr α] : Repr { x : α // P x} where
  reprPrec x n := inst.reprPrec x n
