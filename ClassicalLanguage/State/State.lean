import Mathlib.Data.Int.Basic

-- Program memory state
def State := String → ℤ

-- This function describes a state2 based on state1
-- State2 is the same as state1, but one given name is assigned one given value.
def replS: State → String → ℤ → State
| st, name, val => (fun s:String => if(s==name) then val else st s)
