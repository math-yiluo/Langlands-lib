/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficientLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.TowerIsoLifting

/-!
# Lattices of `ℓ`-adic towers of locally constant sheaves are locally `ℤ_ℓ,X`

The sheaf of abelian groups underlying `ℤ_ℓ,X` is the limit of the tower `n ↦ (ℤ/ℓⁿ)_X` of
abelian sheaves (`AlgebraicGeometry.ProEtale.isLimitPadicIntAbSheafCone`), the forgetful functor
from sheaves of rings to abelian sheaves preserving limits.

Consequently, for a tower `(Gₙ)` of pro-étale abelian sheaves with `Gₙ₊₁/ℓⁿ ≅ Gₙ` (locally, as
cokernels) and `Gₙ` locally isomorphic to `(ℤ/ℓⁿ)_X`, the limit `lim Gₙ` is pro-étale locally
isomorphic to `ℤ_ℓ,X` (`AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_padicIntAbSheaf`),
provided the constant tower `(ℤ/ℓⁿ)_X` itself satisfies the two hypotheses of
`ProEtale.exists_cover_nonempty_iso_overPullback_limit_of_isColimit_cokernelCofork`:
its transitions are locally cokernels of `ℓⁿ`, and its automorphisms (multiplication by units
of `C(-, ℤ/ℓⁿ)`) lift locally. These two facts about the constant tower are stated as
hypotheses here; the first is proved in
`WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowAbSheafCokernel`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {D E : Type*} [Category* D]
  [Category* E] (F : D ⥤ E) [J.HasSheafCompose F]

/-- Postcomposition of sheaves with a functor preserving limits of shape `K` preserves limits of
shape `K`: limits of sheaves are computed on sections. -/
instance preservesLimitsOfShape_sheafCompose {K : Type*} [Category* K] [HasLimitsOfShape K D]
    [HasLimitsOfShape K E] [PreservesLimitsOfShape K F] :
    PreservesLimitsOfShape K (sheafCompose J F) := by
  have : PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J E) :=
    preservesLimitsOfShape_of_natIso
      (Iso.refl (sheafToPresheaf J D ⋙ (Functor.whiskeringRight _ _ _).obj F))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J E)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The tower `n ↦ (ℤ/ℓⁿ)_X` of abelian sheaves on `X_proét`. -/
noncomputable abbrev zmodPowAbSheafDiagram : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  zmodPowSheafDiagram X l ⋙ sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})

/-- The abelian sheaf underlying `ℤ_ℓ,X`. -/
noncomputable abbrev padicIntAbSheaf : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntSheaf X l)

/-- **`ℤ_ℓ,X = lim_n (ℤ/ℓⁿ)_X` as abelian sheaves**: the forgetful functor from sheaves of rings
to abelian sheaves preserves limits. -/
noncomputable def isLimitPadicIntAbSheafCone :
    IsLimit ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapCone
      (padicIntSheafCone X l)) :=
  isLimitOfPreserves _ (isLimitPadicIntSheafCone X l)

/-- The limit of the tower `(ℤ/ℓⁿ)_X` of abelian sheaves is the abelian sheaf `ℤ_ℓ,X`. -/
noncomputable def limitZmodPowAbSheafDiagramIso :
    limit (zmodPowAbSheafDiagram X l) ≅ padicIntAbSheaf X l :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitPadicIntAbSheafCone X l)

/-- **An `ℓ`-adic tower of locally constant sheaves of rank one has a lattice which is locally
`ℤ_ℓ,X`.** Let `(Gₙ)` be a tower of pro-étale abelian sheaves whose transitions are, locally,
cokernels of `ℓⁿ` (i.e. `Gₙ₊₁/ℓⁿ ≅ Gₙ`), with each `Gₙ` locally isomorphic to `(ℤ/ℓⁿ)_X`. Assume
that the constant tower `(ℤ/ℓⁿ)_X` has the same cokernel property (`hR`) and that its
automorphisms lift locally (`haut`). Then `lim Gₙ` is isomorphic to `ℤ_ℓ,X` over the members of
a pro-étale cover of any object. -/
theorem exists_cover_nonempty_iso_padicIntAbSheaf
    (G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1})
    (hR : ∀ (n : ℕ) (Y : X.ProEt), ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫
        ((ProEt.topology X).overPullback Ab.{u + 1} Y).map
          ((zmodPowAbSheafDiagram X l).map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hG : ∀ (n : ℕ) (Y : X.ProEt), ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫
        ((ProEt.topology X).overPullback Ab.{u + 1} Y).map (G.map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (V : X.ProEt), ∃ S ∈ ProEt.topology X V,
      ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
        Nonempty ((isoPresheaf ((zmodPowAbSheafDiagram X l).obj (op n)) (G.obj (op n))).obj
          (op Y)))
    (haut : ∀ (n : ℕ) (Y : X.ProEt) (α : (isoPresheaf ((zmodPowAbSheafDiagram X l).obj (op n))
        ((zmodPowAbSheafDiagram X l).obj (op n))).obj (op Y)),
      ∃ S ∈ ProEt.topology X Y, ∀ ⦃Z : X.ProEt⦄ (h : Z ⟶ Y), S h →
        ∃ β : (isoPresheaf ((zmodPowAbSheafDiagram X l).obj (op (n + 1)))
            ((zmodPowAbSheafDiagram X l).obj (op (n + 1)))).obj (op Z),
          β.hom ≫ ((ProEt.topology X).overPullback Ab.{u + 1} Z).map
              ((zmodPowAbSheafDiagram X l).map (homOfLE n.le_succ).op) =
            ((ProEt.topology X).overPullback Ab.{u + 1} Z).map
                ((zmodPowAbSheafDiagram X l).map (homOfLE n.le_succ).op) ≫
              ((isoPresheaf _ _).map h.op α).hom)
    (V : X.ProEt) :
    ∃ (ι : Type u) (W : ι → X.ProEt) (f : ∀ i, W i ⟶ V),
      Sieve.ofArrows W f ∈ ProEt.topology X V ∧
      ∀ i, Nonempty (((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (limit G) ≅
        ((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (padicIntAbSheaf X l)) := by
  obtain ⟨ι, W, f, hcov, h⟩ :=
    exists_cover_nonempty_iso_overPullback_limit_of_isColimit_cokernelCofork
      (zmodPowAbSheafDiagram X l) G (fun n ↦ ((l ^ n : ℕ) : ℤ)) hR hG hloc haut V
  exact ⟨ι, W, f, hcov, fun i ↦ ⟨(h i).some.symm ≪≫
    ((ProEt.topology X).overPullback Ab.{u + 1} (W i)).mapIso
      (limitZmodPowAbSheafDiagramIso X l)⟩⟩

end AlgebraicGeometry.ProEtale
