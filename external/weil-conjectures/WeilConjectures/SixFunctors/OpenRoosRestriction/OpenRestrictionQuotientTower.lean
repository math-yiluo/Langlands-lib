/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import all WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryQuotientModuleComparison
import all WeilConjectures.SixFunctors.OpenRestrictionCompleteness.OpenRestrictionCompleteness
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # The augmented quotient tower under normalized open restriction

Source: Stacks Project, Tags 03EL, 07A4 and 099N (5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.IntegralOnSlice.reductionWitness
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenRoosRestriction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
  (o : IntegralOpenReduction.Operations l E e)

open IntegralOnSlice

private abbrev F : Mod l E W none ⥤ Mod l E V none :=
  IntegralOpenReduction.restriction l E e o
private instance : (F l E e o).Additive :=
  IntegralOpenReduction.restrictionAdditive l E e o

private abbrev G := (F l E e o).mapHomologicalComplex (.up ℤ)

private instance : PreservesFiniteColimits (F l E e o) := by
  let hL : PreservesFiniteColimits (SheafOfModules.localizedSystemRestriction.{t+1, t,
      max u (t+1)} (completedIntegralCommRingSheafUnrestricted l E W)
      (IntegralOpenReduction.openObject e)) :=
    SheafOfModules.localizedSystemRestrictionColimits _ _
  let : PreservesColimitsOfSize.{0, 0} o.integral.inverse :=
    o.integral.symm.toAdjunction.leftAdjoint_preservesColimits
  let hI : PreservesFiniteColimits o.integral.inverse := inferInstance
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ hL hI

private theorem map_power (n : ℕ) (M : Mod l E W none) :
    (F l E e o).map (uniformizerPower l E W n M) =
      uniformizerPower l E V n ((F l E e o).obj M) := by
  let R := completedIntegralCoefficientSheafUnrestricted l E V
  let S := (completedIntegralCoefficientSheafUnrestricted l E W).over
    (IntegralOpenReduction.openObject e)
  let φ : S ⟶ ((IntegralOpenReduction.sliceSite e).sheafPushforwardContinuous RingCat
      ((ProEt.topology W).over (IntegralOpenReduction.openObject e)) (ProEt.topology V)).obj R :=
    (sheafCompose _ (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
      o.completedMap
  let L := SheafOfModules.localizedSystemRestriction
    (completedIntegralCommRingSheafUnrestricted l E W) (IntegralOpenReduction.openObject e)
  refine OpenRestrictionCompleteness.inverse_scalar (S := S) (R := R)
    (IntegralOpenReduction.sliceSite e) φ o.integral o.integralFunctor (L.obj M)
    (L.map (uniformizerPower l E W n M)) _
    (fun Z ↦ uniformizerSection l E W (op Z.unop.left) ^ (n + 1))
    (fun Z ↦ uniformizerSection l E V Z ^ (n + 1)) ?_ ?_ ?_
  · intro Z x
    rfl
  · intro Z x
    rfl
  · intro Z
    change o.completedMap.hom.app Z
      (integralCompletionScalarValue l E W (op Z.unop.left) ^ (n + 1)) =
        integralCompletionScalarValue l E V
          ((IntegralOpenReduction.sliceSite e).op.obj Z) ^ (n + 1)
    exact (map_pow (o.completedMap.hom.app Z).hom _ (n + 1)).trans
      (congrArg (fun x ↦ x ^ (n + 1))
        (OpenRestrictionCompleteness.scalar_transport l E e o Z.unop))

private theorem mappedCokernel (n : ℕ) (M : Mod l E W none) :
    ∃ h : uniformizerPower l E V n ((F l E e o).obj M) ≫
        (F l E e o).map ((quotientUnit l E W n).app M) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((F l E e o).map ((quotientUnit l E W n).app M)) h)) := by
  obtain ⟨h, ⟨hc⟩⟩ := quotientUnit_isCokernel l E W n M
  have h' : uniformizerPower l E V n ((F l E e o).obj M) ≫
      (F l E e o).map ((quotientUnit l E W n).app M) = 0 := by
    rw [← map_power, ← Functor.map_comp, h, Functor.map_zero]
  refine ⟨h', ⟨?_⟩⟩
  have hh := CokernelCofork.mapIsColimit _ hc (F l E e o)
  let d {N : Mod l E V none} (g : (F l E e o).obj M ⟶ N)
      (hg : uniformizerPower l E V n ((F l E e o).obj M) ≫ g = 0) :=
    CokernelCofork.IsColimit.desc' hh g (by rw [map_power]; exact hg)
  exact CokernelCofork.IsColimit.ofπ _ h' (fun g hg ↦ (d g hg).1)
    (fun g hg ↦ (d g hg).2)
    (fun g hg m hm ↦ Cofork.IsColimit.hom_ext hh (hm.trans (d g hg).2.symm))

private def component (n : ℕ) (M : Mod l E W none) :
    (F l E e o).obj ((ordinaryQuotientModule l E W n).obj M) ≅
      (ordinaryQuotientModule l E V n).obj ((F l E e o).obj M) :=
  (mappedCokernel l E e o n M).choose_spec.some.coconePointUniqueUpToIso
    (quotientUnit_isCokernel l E V n ((F l E e o).obj M)).choose_spec.some

private theorem component_unit (n : ℕ) (M : Mod l E W none) :
    (F l E e o).map ((quotientUnit l E W n).app M) ≫
      (component l E e o n M).hom =
        (quotientUnit l E V n).app ((F l E e o).obj M) :=
  (mappedCokernel l E e o n M).choose_spec.some.comp_coconePointUniqueUpToIso_hom
    (quotientUnit_isCokernel l E V n ((F l E e o).obj M)).choose_spec.some
    WalkingParallelPair.one

attribute [local irreducible] component

private def moduleComparison (n : ℕ) :
    ordinaryQuotientModule l E W n ⋙ F l E e o ≅
      F l E e o ⋙ ordinaryQuotientModule l E V n :=
  NatIso.ofComponents (component l E e o n) (by
    intro M N a
    obtain ⟨h, ⟨hc⟩⟩ := mappedCokernel l E e o n M
    apply Cofork.IsColimit.hom_ext hc
    simp only [Cofork.π_ofπ]
    change (F l E e o).map ((quotientUnit l E W n).app M) ≫
        ((F l E e o).map ((ordinaryQuotientModule l E W n).map a) ≫
          (component l E e o n N).hom) =
      (F l E e o).map ((quotientUnit l E W n).app M) ≫
        ((component l E e o n M).hom ≫
          (ordinaryQuotientModule l E V n).map ((F l E e o).map a))
    rw [← Category.assoc, ← Functor.map_comp, ← (quotientUnit l E W n).naturality,
      Functor.map_comp, Category.assoc, component_unit, ← Category.assoc, component_unit]
    exact (quotientUnit l E V n).naturality ((F l E e o).map a))

private def levelComparison (n : ℕ) :
    level l E W none n ⋙ G l E e o ≅ G l E e o ⋙ level l E V none n :=
  NatIso.mapHomologicalComplex (moduleComparison l E e o n) (.up ℤ)

private theorem augmentation_f (T : Scheme.{t}) (P : Cx l E T none) (n : ℕ) (i : ℤ) :
    (((augmentation l E T none).app P).app (op n)).f i =
      (quotientUnit l E T n).app (P.X i) := by
  ext Z x
  exact (augmentation_existsUnique l E T none).exists.choose_spec P n i Z x

private theorem levelComparison_unit (P : Cx l E W none) (n : ℕ) :
    (G l E e o).map (((augmentation l E W none).app P).app (op n)) ≫
        (levelComparison l E e o n).hom.app P =
      ((augmentation l E V none).app ((G l E e o).obj P)).app (op n) := by
  apply HomologicalComplex.hom_ext
  intro i
  change (F l E e o).map ((((augmentation l E W none).app P).app (op n)).f i) ≫
      (component l E e o n (P.X i)).hom = _
  rw [augmentation_f, augmentation_f]
  exact component_unit l E e o n (P.X i)

attribute [local irreducible] levelComparison

private theorem augmentation_step (T : Scheme.{t}) (P : Cx l E T none) (n : ℕ) :
    ((augmentation l E T none).app P).app (op (n + 1)) ≫
        ((tower l E T none).obj P).map (homOfLE (Nat.le_succ n)).op =
      ((augmentation l E T none).app P).app (op n) := by
  have h := ((augmentation l E T none).app P).naturality
    (homOfLE (Nat.le_succ n)).op
  exact (Category.id_comp _).symm.trans h |>.symm

private theorem levelComparison_step (P : Cx l E W none) (n : ℕ) :
    (G l E e o).map (((tower l E W none).obj P).map
        (homOfLE (Nat.le_succ n)).op) ≫ (levelComparison l E e o n).hom.app P =
      (levelComparison l E e o (n + 1)).hom.app P ≫
        ((tower l E V none).obj ((G l E e o).obj P)).map
          (homOfLE (Nat.le_succ n)).op := by
  have hi (i : ℤ) : Epi (((G l E e o).map
      (((augmentation l E W none).app P).app (op (n + 1)))).f i) := by
    change Epi ((F l E e o).map
      ((((augmentation l E W none).app P).app (op (n + 1))).f i))
    rw [augmentation_f]
    exact epi_of_isColimit_cofork (mappedCokernel l E e o (n + 1) (P.X i)).choose_spec.some
  let : Epi ((G l E e o).map
      (((augmentation l E W none).app P).app (op (n + 1)))) :=
    HomologicalComplex.epi_of_epi_f _ hi
  apply (cancel_epi ((G l E e o).map
    (((augmentation l E W none).app P).app (op (n + 1))))).1
  have h₁ := congrArg (fun f ↦ f ≫ (levelComparison l E e o n).hom.app P)
    ((G l E e o).map_comp
      (((augmentation l E W none).app P).app (op (n + 1)))
      (((tower l E W none).obj P).map (homOfLE (Nat.le_succ n)).op)).symm
  have h₂ := congrArg (fun f ↦ (G l E e o).map f ≫
    (levelComparison l E e o n).hom.app P) (augmentation_step l E W P n)
  have h₃ := (augmentation_step l E V ((G l E e o).obj P) n).symm
  have h₄ := congrArg (fun f ↦ f ≫
    ((tower l E V none).obj ((G l E e o).obj P)).map
      (homOfLE (Nat.le_succ n)).op) (levelComparison_unit l E e o P (n + 1)).symm
  apply Eq.trans (Category.assoc _ _ _).symm
  apply Eq.trans (h₁.trans (h₂.trans
    ((levelComparison_unit l E e o P n).trans (h₃.trans h₄))))
  exact Category.assoc _ _ _

private def towerComparison :
    tower l E W none ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj (G l E e o) ≅
      G l E e o ⋙ tower l E V none := by
  let α (P : Cx l E W none) :
      (tower l E W none).obj P ⋙ G l E e o ⟶
        (tower l E V none).obj ((G l E e o).obj P) :=
    NatTrans.ofOpSequence (fun n ↦ (levelComparison l E e o n).hom.app P)
      (fun n ↦ levelComparison_step l E e o P n)
  have hα (P) : IsIso (α P) := by
    have hi (n : ℕᵒᵖ) : IsIso ((α P).app n) := by
      change IsIso ((levelComparison l E e o n.unop).hom.app P)
      infer_instance
    exact NatIso.isIso_of_isIso_app (α P)
  exact NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (α P) (hα P)) (by
    intro P Q a
    apply NatTrans.ext
    funext n
    exact (levelComparison l E e o n.unop).hom.naturality a)

/-- Restriction commutes with the ordinary strict quotient tower and its augmentation.
Source: Stacks Project, sites-modules.tex, Tag 03EL; sites-cohomology.tex, Tag 07A4;
proetale.tex, Tag 099N (5).
(blueprint: lem-sf-open-restriction-quotient-tower).

Proof: the normalized quotient-unit map is a cokernel of multiplication by
uniformizer^(n+1), by the proved ordinary quotient-module calculation. The completed
coefficient map preserves the uniformizer, as can be checked against its finite
projections and their constant-section equations. The supplied module equivalence
therefore transports the uniformizer endomorphism, including all its powers.
Restriction preserves finite colimits, so its image of the quotient unit is another
cokernel of the same endomorphism. The unique comparison of these cokernels gives
the natural module isomorphism carrying quotient unit to quotient unit.
Apply it termwise to complexes. The augmentation at every degree is precisely the
quotient unit. Precompose the desired consecutive transition square with the image
of the augmentation at n+1. It is an epimorphism, since it is a cokernel. Both
composites become the augmentation at n by naturality of the tower augmentation
and the comparison's unit equation. Cancel this epimorphism. The consecutive
squares assemble to one natural isomorphism of strict towers, retaining the
augmentation equations. This uses no resolutions, Roos complexes or derived
descent, and works for zero modules, the empty open, and n=0 (exponent one). -/
theorem quotientTower :
    ∃ τ : IntegralOnSlice.tower l E W none ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)) ≅
      (IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ) ⋙
        IntegralOnSlice.tower l E V none,
      ∀ (P : IntegralOnSlice.Cx l E W none) (n : ℕ),
        ((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)).map
            (((IntegralOnSlice.augmentation l E W none).app P).app (op n)) ≫
          (τ.hom.app P).app (op n) =
        ((IntegralOnSlice.augmentation l E V none).app
          (((IntegralOpenReduction.restriction l E e o).mapHomologicalComplex (.up ℤ)).obj P)).app
            (op n) := by
  exact ⟨towerComparison l E e o, levelComparison_unit l E e o⟩

end WeilConjectures.OpenRoosRestriction
