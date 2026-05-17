import Tommy.Torus

-- Check what type S1 is and what Cylinder.1 is
#check @Cylinder  -- S1 × Set.Icc (0:ℝ) 1
-- c.1 : ↥S1 
example (c : Cylinder) : c.1 ∈ S1 := c.1.2
-- torus_proj should map FareyTorus → ↥S1
#check (fun (c : Cylinder) => c.1)  -- Cylinder → ↥S1

