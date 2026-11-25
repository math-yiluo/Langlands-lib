/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.AlgebraicGeometry.Lisse.LisseProjectiveConstantModels
import all WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels

/-! # Finite projective cover data for an étale lisse sheaf

Source: blueprint scalar-six-ctf (1), finite projective local models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [Finite A]

/-- A finite projective étale lisse sheaf has a pro-étale cover by finite projective
constant ordinary modules.  This is the cover and module data used by the scalar
comparison construction below.

Source: blueprint scalar-six-ctf (1), finite ring generators; Stacks 00NX and 099Y.

Proof: choose the locally constant datum supplied by the étale lisse hypothesis,
replace each geometric stalk by the corresponding finite projective constant module,
and regard the resulting étale cover as a pro-étale cover.  The empty chart uses the
zero module.  The comparison isomorphisms are stable under refinement of the cover. -/
theorem finiteEtaleLisseScalarComparisonData
    (S : Scheme.{u}) [IsNoetherian S]
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (hL : FlatModelEtaleLisseProjective (ULift.{u + 1} A) L) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ j : 𝒰.I₀,
      ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A),
        Module.Finite (ULift.{u + 1} A) P ∧
        Module.Projective (ULift.{u + 1} A) P ∧
        Nonempty ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝒰.f j)).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S).obj L) ≅
          (constantSheaf (Scheme.ProEt.topology (𝒰.X j))
            (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P) := by
  obtain ⟨d, hd⟩ := AlgebraicGeometry.lisseProjective_constantModels
    (ULift.{u + 1} A) L hL
  let 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S :=
    { I₀ := d.cover.I₀
      X := d.cover.X
      f := d.cover.f
      mem₀ := Scheme.etalePrecoverage_le_proetalePrecoverage _ d.cover.mem₀ }
  refine ⟨𝒰, fun j ↦ ?_⟩
  obtain ⟨P, hfin, hproj, ⟨i⟩⟩ := hd j
  let V := d.cover.etalePrecoverageToEtale j
  let E := (Scheme.Etale.overSheafEquiv V (ModuleCat.{u + 1} (ULift.{u + 1} A))).functor
  let iL : (AlgebraicGeometry.Etale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) V.hom).obj L ≅
      (constantSheaf V.left.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P :=
    (Scheme.overSheafEquivFunctorObjOverIso
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) V L).symm ≪≫
    E.mapIso i ≪≫ ((Scheme.Etale.overEquiv V).constantSheafSheafCongrIso
      (S.smallEtaleTopology.over V) V.left.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) Over.mkIdTerminal).app P
  exact ⟨P, hfin, hproj, ⟨
    (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) V.hom).app L ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) V.left).mapIso iL ≪≫
    (Scheme.comparisonConstantIso V.left (ULift.{u + 1} A)).app P⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
