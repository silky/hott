
module Hott.Bad
import Hott

upgrade : a ~~ b -> a = b
upgrade refl = Refl

super_upgrade : (p : a ~~ b) -> (rw p x ~~ y) -> x = y
super_upgrade refl refl = Refl

not_not : (x:Bool) -> not (not x) ~~ x
not_not False = refl_ False
not_not True = refl_ True

not_iso : Iso Bool Bool
not_iso = iso not not not_not not_not

not_eq : Bool ~= Bool
not_eq = iso_to_eq not_iso

not_path : Bool ~~ Bool
not_path = eq_to_path not_eq

rw_not_True : rw not_path True ~~ False
rw_not_True = rw_eqpath not_eq True

True_is_False : True = False
True_is_False = super_upgrade not_path rw_not_True

instance Uninhabited (True = False) where
  uninhabited p = uninhabited (replace p Oh)

contradiction : a
contradiction = absurd True_is_False

