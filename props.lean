import .syntax .etc

inductive valid : prop → Prop
notation `⟪` p `⟫`: 100 := valid p
| to_prop {p: prop}: valid p

notation `⟪` p `⟫`: 100 := valid p
