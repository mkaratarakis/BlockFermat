def NoZeroDivisors.toCancelMonoidWithZero [Ring α] [NoZeroDivisors α] : CancelMonoidWithZero α :=
  { (by infer_instance : MonoidWithZero α) with
    mul_left_cancel_of_ne_zero := fun ha =>
      @IsRegular.left _ _ _ (isRegular_of_ne_zero' ha) _ _,
    mul_right_cancel_of_ne_zero := fun hb =>
      @IsRegular.right _ _ _ (isRegular_of_ne_zero' hb) _ _ }
#align no_zero_divisors.to_cancel_monoid_with_zero NoZeroDivisors.toCancelMonoidWithZero

def NoZeroDivisors.toCancelCommMonoidWithZero [CommRing α] [NoZeroDivisors α] :
    CancelCommMonoidWithZero α :=
  { NoZeroDivisors.toCancelMonoidWithZero, ‹CommRing α› with }
#align no_zero_divisors.to_cancel_comm_monoid_with_zero NoZeroDivisors.toCancelCommMonoidWithZero