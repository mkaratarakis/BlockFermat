def orderBot [PartialOrder α] {a b : α} (h : a < b) : OrderBot (Ico a b) :=
  (isLeast_Ico h).orderBot
#align set.Ico.order_bot Set.Ico.orderBot

def orderTop [PartialOrder α] {a b : α} (h : a < b) : OrderTop (Ioc a b) :=
  (isGreatest_Ioc h).orderTop
#align set.Ioc.order_top Set.Ioc.orderTop

def orderBot [Preorder α] {a b : α} (h : a ≤ b) : OrderBot (Icc a b) :=
  (isLeast_Icc h).orderBot
#align set.Icc.order_bot Set.Icc.orderBot

def orderTop [Preorder α] {a b : α} (h : a ≤ b) : OrderTop (Icc a b) :=
  (isGreatest_Icc h).orderTop
#align set.Icc.order_top Set.Icc.orderTop

def boundedOrder [Preorder α] {a b : α} (h : a ≤ b) : BoundedOrder (Icc a b) :=
  { Icc.orderTop h, Icc.orderBot h with }
#align set.Icc.bounded_order Set.Icc.boundedOrder