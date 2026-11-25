/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
import WeilConjectures.SixFunctors.Sf.SfClopenScalarModuleComparison

/-! # Chain quotient comparison on a clopen component

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 03EL.
(blueprint: lem-sf-clopen-scalar-chain-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures
private def sfClopenScalarRestrictionSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (d : SfClopenCoefficientRestriction l E T U) (n : ℕ) :
    scalarReductionRestriction l E T n ⋙
        sfClopenModuleRestriction U (completedIntegralCoefficientSheafUnrestricted l E T)
          (completedIntegralCoefficientSheafUnrestricted l E U.toScheme) d.completion ≅
      sfClopenModuleRestriction U _ _ (d.finite n) ⋙
        scalarReductionRestriction l E U.toScheme n := by
  let F := scalarReductionRestriction l E T n ⋙
    sfClopenModuleRestriction U (completedIntegralCoefficientSheafUnrestricted l E T)
      (completedIntegralCoefficientSheafUnrestricted l E U.toScheme) d.completion
  let G := sfClopenModuleRestriction U _ _ (d.finite n) ⋙
    scalarReductionRestriction l E U.toScheme n
  change F ≅ G
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ ?_) ?_)) ?_
  · let A := (F.obj M).val.obj V
    let B := (G.obj M).val.obj V
    refine
      { hom := ConcreteCategory.ofHom (X := A) (Y := B) ?_
        inv := ConcreteCategory.ofHom (X := B) (Y := A) ?_
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · refine { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := ?_ }
      intro a x
      have h := congrArg (fun f ↦ f.hom.app V a) (d.projection n)
      exact congrArg (fun r ↦ r •
        (show M.val.obj ((sfClopenSiteInclusion U).op.obj V) from x)) h
    · refine { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := ?_ }
      intro a x
      have h := congrArg (fun f ↦ f.hom.app V a) (d.projection n)
      exact congrArg (fun r ↦ r •
        (show M.val.obj ((sfClopenSiteInclusion U).op.obj V) from x)) h.symm
    · ext x
      rfl
    · ext x
      rfl
  · intro V W f
    ext x
    rfl
  · intro M N f
    ext V x
    rfl

/-- Completed-coefficient chain quotients commute with restriction, with the tensor formula.

Source: Stacks Project, sites-modules.tex, Tags 03EL and 03CY;
sites-cohomology.tex, Tag 06YY.
(blueprint: lem-sf-clopen-scalar-chain-comparison).

Proof: `d.projection` identifies the two completed scalar actions on a finite module.
Identity maps on sections therefore define a natural scalar-restriction square. Apply
that square and the normalized ordinary scalar comparison degreewise to the finite
quotient complex. The first map acts by the identity on sections, so the tensor formula
is precisely the ordinary comparison formula in each degree. -/
theorem sf_clopen_scalar_chain_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (d : SfClopenCoefficientRestriction l E T U) :
    ∃ (quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
      (sfClopenComplexRestriction d).obj (unrestrictedTowerComplex l E T n P) ≅
        unrestrictedTowerComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P)),
      (∀ P n q V s x, (((quotient P n).hom.f q).val.app (op V))
        (unrestrictedTowerTensorSection l E T n (P.X q)
          (op ((sfClopenSiteInclusion U).obj V)) ((d.finite n).hom.hom.app (op V) s) x) =
        unrestrictedTowerTensorSection l E U.toScheme n
          (((sfClopenComplexRestriction d).obj P).X q) (op V) s x) := by
  classical
  let := fun n ↦ scalarReductionExtensionAdditive l E T n
  let := fun n ↦ scalarReductionExtensionAdditive l E U.toScheme n
  let := d.additive
  let := d.finite_additive
  choose c hc using sf_clopen_scalar_module_comparison l E T U d
  let finiteQuotient (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :=
    (NatIso.mapHomologicalComplex (c n) (.up ℤ)).app P
  let quotient (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :=
    (NatIso.mapHomologicalComplex (sfClopenScalarRestrictionSquare l E T U d n)
      (.up ℤ)).app (unrestrictedTowerFiniteComplex l E T n P) ≪≫
      ((scalarReductionRestriction l E U.toScheme n).mapHomologicalComplex
        (.up ℤ)).mapIso (finiteQuotient P n)
  refine ⟨quotient, ?_⟩
  intro P n q V s x
  exact hc n (P.X q) V s x
end WeilConjectures
