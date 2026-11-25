/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedDirectImagePreservesCompleteness
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProductsOfUniverses
import Mathlib.Data.Nat.Prime.Infinite
/-! # Completeness of quasi-compact integral open extension

Source: Stacks proetale.tex Tag 09BP and algebraization.tex Tag 0A0E. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOpenReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
private theorem scalar_projection (T : Scheme.{t}) (n : ℕ) (V : T.ProEtᵒᵖ) :
    (completedIntegralCommRingProjectionUnrestricted l E T n).hom.app V
      (integralCompletionScalarValue l E T V) =
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1)))))).app V
      (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n+1))
        (Padic.coefficientExtensionUniformizer l E))) := by
  let B := CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionIntegers l E))
  let C := CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1)))
  let q : B ⟶ C := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{t+1} _ ≃+* _).symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n+1))).comp
        (ULift.ringEquiv : ULift.{t+1} _ ≃+* _).toRingHom))
  have hq : integralConstantToCompletionOfUniverses l E T ≫
      limit.π (integralCoefficientSheafSystem l E T) (op n) =
        integralConstantQuotientOfUniverses l E T n := limit.lift_π _ _
  have hh := congrArg (fun f ↦ f.hom.app V
    ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj B)).app V
      (ULift.up (Padic.coefficientExtensionUniformizer l E)))) hq
  change _ = (integralConstantQuotientOfUniverses l E T n).hom.app V _ at hh
  change (completedIntegralCommRingProjectionUnrestricted l E T n).hom.app V
      (integralCompletionScalarValue l E T V) = _ at hh
  rw [hh]
  exact congrArg (fun f ↦ f.app V
    (ULift.up (Padic.coefficientExtensionUniformizer l E)))
      (toSheafify_naturality (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).map q)).symm

private theorem scalar_slice (o : Operations l E j)
    (V : (Over (openObject j))ᵒᵖ) :
    o.completedMap.hom.app V (integralCompletionScalarValue l E X (op V.unop.left)) =
      integralCompletionScalarValue l E U ((sliceSite j).op.obj V) := by
  let ev := sheafToPresheaf (ProEt.topology U) RingCat.{max u (t+1)} ⋙
    (CategoryTheory.evaluation U.ProEtᵒᵖ RingCat.{max u (t+1)}).obj
      ((sliceSite j).op.obj V)
  apply Concrete.isLimit_ext _ (isLimitOfPreserves ev
    (limit.isLimit (integralCoefficientSheafSystem l E U)))
  intro n
  have hp := congrArg (fun f ↦ f.hom.app V
    (integralCompletionScalarValue l E X (op V.unop.left))) (o.projections n.unop)
  change (completedIntegralCommRingProjectionUnrestricted l E U n.unop).hom.app
      ((sliceSite j).op.obj V)
      (o.completedMap.hom.app V (integralCompletionScalarValue l E X (op V.unop.left))) =
    (o.finiteMap n.unop).hom.app V
      ((completedIntegralCommRingProjectionUnrestricted l E X n.unop).hom.app
        (op V.unop.left) (integralCompletionScalarValue l E X (op V.unop.left))) at hp
  change (completedIntegralCommRingProjectionUnrestricted l E U n.unop).hom.app
      ((sliceSite j).op.obj V) _ =
    (completedIntegralCommRingProjectionUnrestricted l E U n.unop).hom.app
      ((sliceSite j).op.obj V) _
  rw [hp, scalar_projection, scalar_projection]
  exact congrArg (fun f ↦ f
    (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop+1))
      (Padic.coefficientExtensionUniformizer l E)))) (o.finiteConstants n.unop V.unop)

private theorem scalar_extension (o : Operations l E j)
    (P : IntegralOnSlice.Cx l E U none) :
    End.of (((extension l E j o).mapHomologicalComplex (.up ℤ)).map
      (integralKoszulScalar l E U P).asHom) =
    integralKoszulScalar l E X
      (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply End.ext
  apply HomologicalComplex.hom_ext
  intro i
  let L := SheafOfModules.localizedSystemExtension.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X) (openObject j)
  let R := SheafOfModules.localizedSystemRestriction.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X) (openObject j)
  let adj : L ⊣ R := SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X) (openObject j)
  let M := o.integral.functor.obj (P.X i)
  have hF' (F : scalarReductionSource l E U ⥤
      SheafOfModules.{max u (t+1)}
        ((completedIntegralCoefficientSheafUnrestricted l E X).over (openObject j)))
      (hF : F = SheafOfModules.pushforward.{max u (t+1)} (F := sliceSite j)
        ((sheafCompose _ (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
          o.completedMap)) :
      ∀ (V : (Over (openObject j))ᵒᵖ) (x : (F.obj (P.X i)).val.obj V),
        (F.map ((integralKoszulScalar l E U P).asHom.f i)).val.app V x =
          integralCompletionScalarValue l E X (op V.unop.left) • x := by
    subst F
    intro V x
    let x₀ : (P.X i).val.obj ((sliceSite j).op.obj V) := x
    change ((integralKoszulScalar l E U P).asHom.f i).val.app
        ((sliceSite j).op.obj V) x₀ =
      o.completedMap.hom.app V
        (integralCompletionScalarValue l E X (op V.unop.left)) • x₀
    have hs := (integralKoszulScalar_existsUnique l E U P).exists.choose_spec
      i ((sliceSite j).op.obj V) x₀
    change ((integralKoszulScalar l E U P).asHom.f i).val.app
      ((sliceSite j).op.obj V) x₀ = _ at hs
    exact hs.trans (congrArg (fun z ↦ z • x₀) (scalar_slice l E j o V)).symm
  have hF := hF' o.integral.functor o.integralFunctor
  change L.map (o.integral.functor.map ((integralKoszulScalar l E U P).asHom.f i)) = _
  apply (adj.homEquiv M (L.obj M)).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit]
  change adj.unit.app M ≫ (L ⋙ R).map _ = _
  rw [← adj.unit.naturality (o.integral.functor.map
    ((integralKoszulScalar l E U P).asHom.f i))]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change (adj.unit.app M).val.app V
      ((o.integral.functor.map ((integralKoszulScalar l E U P).asHom.f i)).val.app V x) =
    ((integralKoszulScalar l E X
      (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj P)).asHom.f i).val.app
        (op V.unop.left) ((adj.unit.app M).val.app V x)
  rw [hF]
  have hs := (integralKoszulScalar_existsUnique l E X
    (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj P)).exists.choose_spec
      i (op V.unop.left) ((adj.unit.app M).val.app V x)
  change ((integralKoszulScalar l E X
    (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj P)).asHom.f i).val.app
      (op V.unop.left) ((adj.unit.app M).val.app V x) = _ at hs
  exact (((adj.unit.app M).val.app V).hom.map_smul _ _).trans hs.symm

private theorem extension_products [QuasiCompact j] (o : Operations l E j) :
    PreservesLimitsOfShape (Discrete ℕ) (extension l E j o) := by
  let L := SheafOfModules.localizedSystemExtension.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X) (openObject j)
  have : IsOpenImmersion (openObject j).hom := by
    change IsOpenImmersion j
    infer_instance
  have : QuasiCompact (openObject j).hom := by
    change QuasiCompact j
    infer_instance
  have : ∀ (M : ℕ → SheafOfModules.{max u (t+1)}
      ((completedIntegralCoefficientSheafUnrestricted l E X).over (openObject j))),
      PreservesLimit (Discrete.functor M) L := by
    intro M
    have := proEtaleRingedExtensionByZero_products_of_universes (openObject j)
      (completedIntegralCommRingSheafUnrestricted l E X) M
    exact PreservesProduct.of_iso_comparison L M
  have : PreservesLimitsOfShape (Discrete ℕ) L := preservesLimitsOfShape_of_discrete L
  change PreservesLimitsOfShape (Discrete ℕ) (o.integral.functor ⋙ L)
  infer_instance

private theorem extension_complete_principal [QuasiCompact j]
    (p : ℕ) [Fact p.Prime] (hpl : p ≠ l) (o : Operations l E j)
    (K : IntegralOnSlice.D l E U none) (hK : complete l E U K) :
    complete l E X ((shriek l E j o).obj K) := by
  classical
  let H := extension l E j o
  let G := H.mapHomologicalComplex (.up ℤ)
  have : PreservesLimitsOfShape (Discrete ℕ) H := extension_products l E j o
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hP : IsDerivedCompleteUnrestricted l E U (DerivedCategory.Q.obj P) :=
    (complete_iff_local p l hpl E U _).mpr
      (integralLocallyComplete_iso l E U _ e.symm
        ((complete_iff_local p l hpl E U K).mp hK))
  let μ := integralKoszulScalar l E U P
  have hμ : QuasiIso (CochainComplex.PrincipalCone.unit μ) :=
    (complete_iff_principalUnit p l hpl E U P).mp hP
  have : QuasiIso (G.map (CochainComplex.PrincipalCone.unit μ)) := inferInstance
  have hscalar : End.of (G.map μ.asHom) = integralKoszulScalar l E X (G.obj P) :=
    scalar_extension l E j o P
  let a : DerivedCategory.Q.obj (G.obj P) ≅ DerivedCategory.Q.obj
      (CochainComplex.PrincipalCone.completion (integralKoszulScalar l E X (G.obj P))) :=
    asIso (DerivedCategory.Q.map (G.map (CochainComplex.PrincipalCone.unit μ))) ≪≫
      DerivedCategory.Q.mapIso (principalMapIso H μ) ≪≫
        DerivedCategory.Q.mapIso (eqToIso (congrArg
          (fun z : End (G.obj P) ↦ CochainComplex.PrincipalCone.completion z) hscalar))
  have hcomplete := (IntegralPrincipalCone.localCriterion l E X
    (integralCompletionScalarValue l E X) (integralScalar_natural l E X)
    (G.obj P) (integralKoszulScalar l E X (G.obj P))
    (integralKoszulScalar_existsUnique l E X (G.obj P)).exists.choose_spec
    (DerivedCategory.Q.obj (G.obj P)) (Iso.refl _)).1
  have hlocal := integralLocallyComplete_iso l E X _ a.symm hcomplete
  exact (complete_iff_local p l hpl E X _).mpr
    (integralLocallyComplete_iso l E X _
      ((H.mapDerivedCategoryFactors.app P).symm ≪≫ H.mapDerivedCategory.mapIso e) hlocal)

/-- Quasi-compact open extension preserves the actual quotient-tower completeness
predicate for the fixed section-normalized operations, at independent universes.
Source: Stacks proetale.tex Tag 09BP, sites-modules.tex Tag 093M,
and algebraization.tex Tag 0A0E; the open case of completedExtensionZeroComparison.
(blueprint: lem-sf-integral-open-extension-complete).

Proof: the quotient-tower completeness predicate is equivalent to local principal
completeness for multiplication by the valuation uniformizer. Choose an arbitrary
complex representing K. Its principal-completion unit is a quasi-isomorphism.
The ordinary open extension is exact, and quasi-compactness makes it preserve
countable products. Its termwise functor therefore preserves the unit's
quasi-isomorphism and commutes with the cone, shift, and product construction of
principal completion. The completed coefficient projection equations, followed by
the finite constant-section equations, show that its coefficient transport preserves
the actual uniformizer section. The localized open adjunction and linearity of its
unit then show that extension carries the source scalar chain map to the target
scalar chain map. Thus the target representative is isomorphic in the derived
category to its principal completion. Principal completion is locally complete;
transport along this isomorphism and then along the exact-derived computation
isomorphism proves completeness of extension. Neither equality of the site and
coefficient universes nor boundedness is used. The same universal properties cover
the empty open and the identity open. -/
theorem integralOpenExtensionComplete [QuasiCompact j]
    (_hlX : IsUnit (l : Γ(X, ⊤))) (_hlU : IsUnit (l : Γ(U, ⊤))) (o : Operations l E j) :
    ∀ K, complete l E U K → complete l E X ((shriek l E j o).obj K) := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  have hne : p ≠ l := by omega
  exact extension_complete_principal l E j p hne o

end WeilConjectures.IntegralOpenReduction
