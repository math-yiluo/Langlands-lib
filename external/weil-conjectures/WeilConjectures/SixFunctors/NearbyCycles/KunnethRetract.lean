/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Retract
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback

/-!

# The Künneth map of nearby cycles and retracts

Let `ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P` be morphisms of models compatible with
`φ₁ : P ⟶ M`, `φ₂ : P ⟶ N` and `φ₁' : P' ⟶ M'`, `φ₂' : P' ⟶ N'`. The pullback of the Künneth
map `Lρ'^* Π_{A,B}` and the Künneth map `Π' = Π_{Lρ_M^* A, Lρ_N^* B}` fit into the square of
`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`, whose vertical maps are built from the
pullback exchanges `α_{ρ_M}`, `α_{ρ_N}`, `α_{ρ_P}`.

When the exchanges are not invertible, but `α_{ρ_N}` is and `α_{ρ_M}`, `α_{ρ_P}` are split
monomorphisms whose retractions are compatible with `Π'`, the map `Lρ'^* Π_{A,B}` is still a
retract of `Π'`, hence invertible if `Π'` is
(`NearbyCyclesModel.isIso_map_kunnethMap_of_isTensorRetract`). This is the shape of the
generic-slicing step of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Finite support"): there `α_{ρ_M}` and
`α_{ρ_P}` are the inclusions of the invariants under a pro-`p` group `P` acting trivially on the
nearby cycles of `N'`, the retractions are the averaging projections, and their compatibility with
`Π'` is the projection formula for invariants (blueprint `prose-E-10`).

The retraction data are predicates on the equation of the square
(`CategoryTheory.IsSquareRetract`, `CategoryTheory.IsTensorRetract`), so that the vertical maps are
read off the square instead of being restated.

## Main statements

* `NearbyCyclesModel.isIso_map_kunnethMap_of_isSquareRetract`,
  `NearbyCyclesModel.isIso_map_kunnethMap_of_isTensorRetract`: the pullback of the Künneth map is
  invertible if the Künneth map of the pullback models is and the retraction data exist.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

-- the Künneth maps of the two products are large terms
/-- **The pullback of the Künneth map is a retract of the Künneth map of the pullback models**:
for morphisms of models `ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P` compatible with
`φ₁`, `φ₂` and `φ₁'`, `φ₂'`, consider the square of the Künneth maps and pullbacks
(`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`)
```
Lρ'^* Π_{A,B} ≫ a = δ ≫ (u_M ⊗ u_N) ≫ Π',
```
where `a` is the pullback exchange `α_{ρ_P}(A ⊠ B)` followed by the tensor and pullback
comparison, `u_M`, `u_N` are the pullback exchanges `α_{ρ_M}(A)`, `α_{ρ_N}(B)` preceded by the
pullback comparisons, `δ` is the monoidal structure of `Lρ'^*` and `Π' = Π_{Lρ_M^* A, Lρ_N^* B}`
is the Künneth map of the pullback models. If `u_M ⊗ u_N` and `a` admit retractions whose
idempotents are compatible with `Π'` (`CategoryTheory.IsSquareRetract`), then `Lρ'^* Π_{A,B}` is
invertible as soon as `Π'` is. -/
theorem isIso_map_kunnethMap_of_isSquareRetract (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂')
    (ρM : MU.Hom M r₁ r₁') (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r')
    (htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total)
    (hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic)
    (htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total)
    (hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic)
    (hb₁ : e₁ ≫ r₁ = r ≫ f₁) (hs₁ : e₁' ≫ r₁' = r' ≫ f₁') (hb₂ : e₂ ≫ r₂ = r ≫ f₂)
    (hs₂ : e₂' ≫ r₂' = r' ≫ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hR : IsSquareRetract (map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN ρP htot₁
      hgen₁ htot₂ hgen₂ hb₁ hs₁ hb₂ hs₂ A B))
    [IsIso (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B))] :
    IsIso (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) :=
  hR.isIso

-- the Künneth maps of the two products are large terms
/-- **The pullback of the Künneth map is a retract of the Künneth map of the pullback models**,
tensor form: in the square of `NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`, if the
pullback exchange `α_{ρ_N}(B)` is invertible and `u_M` and `a` admit retractions whose idempotents
are compatible with `Π'` (`CategoryTheory.IsTensorRetract`), then `Lρ'^* Π_{A,B}` is invertible as
soon as `Π'` is. -/
theorem isIso_map_kunnethMap_of_isTensorRetract (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂')
    (ρM : MU.Hom M r₁ r₁') (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r')
    (htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total)
    (hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic)
    (htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total)
    (hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic)
    (hb₁ : e₁ ≫ r₁ = r ≫ f₁) (hs₁ : e₁' ≫ r₁' = r' ≫ f₁') (hb₂ : e₂ ≫ r₂ = r ≫ f₂)
    (hs₂ : e₂' ≫ r₂' = r' ≫ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hN : IsIso ((ρN.pullbackExchange Λ).app B))
    (hR : IsTensorRetract (map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN ρP htot₁
      hgen₁ htot₂ hgen₂ hb₁ hs₁ hb₂ hs₂ A B))
    (hK : IsIso (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B))) :
    IsIso (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) :=
  hR.isSquareRetract.isIso

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
