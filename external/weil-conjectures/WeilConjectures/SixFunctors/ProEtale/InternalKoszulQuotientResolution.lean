/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.InternalQuotientTowerModel
import WeilConjectures.SixFunctors.ProEtale.InternalKoszulFiniteAcyclicity
import WeilConjectures.SixFunctors.ProEtale.InternalKoszulFiniteAugmentation

/-! # The finite Koszul resolution of the transported actual quotients

Source: integral-models proof (1), Stacks Tags 099L, 099M and 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
local instance finiteResolutionDerived :
    HasDerivedCategory (ConstantCompletion.Mod (ring l E X)) :=
  HasDerivedCategory.standard _
local instance finiteResolutionTowerDerived :
    HasDerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ring l E X)) :=
  HasDerivedCategory.standard _

/-- The strict dual singleton Koszul tower resolves the transported actual quotient
 tower, including the degree-zero augmentation. This statement concerns complexes of
 towers only; it does not involve derived inverse limit or a completion presentation.

Source: integral-models proof (1); Stacks Tags 099L, 099M, 0913 and 0A0E.
(auxiliary; not a blueprint node).

Proof: extract a specified generating section from the kernel ideal on each slice;
its image is a, so a has zero residue. Use koszul_finite_augmentation to construct
the finite maps, their zero
components, their unit identities and their successor compatibility. The sequence
constructor gives a natural transformation of strict towers. Transpose it degreewise
to obtain q. The one-level theorem koszul_finite_augmentation_quasiIso, followed by
evaluation detection of quasi-isomorphisms, proves that q is a quasi-isomorphism.
For the unit equation compose in each complex degree with every limit projection.
The limMap and limit.lift projection identities reduce it to the finite unit equation.
Joint monicity of projections proves the result. No derived inverse limit is used.
-/
theorem koszul_quotient_resolution [IsNoetherian X]
    (a : ((ring l E X).obj ⋙ forget CommRingCat).sections)
    (ha : ∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
      IsRingedIdealGeneratingList (ring l E X)
        (ConstantCompletion.kernelIdeal (residue l E X)).module
        (ConstantCompletion.kernelIdeal (residue l E X)).inclusion U 1
        (fun _ ↦ a.val (op U)))
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E X) (.up ℤ)).kFlat P) :
    ∃ q : ringedKoszulTensorTowerComplex (ring l E X) 1 (fun _ ↦ a)
        (complex l E X P) ⟶ quotientComplex l E X P,
      QuasiIso q ∧
        ringedKoszulLimitUnit (ring l E X) 1 (fun _ ↦ a) (complex l E X P) ≫
          ((lim : (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ring l E X)) ⥤ _).mapHomologicalComplex
            (.up ℤ)).map q = quotientLimitUnit l E X P := by
  have hres (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :
      (residue l E X).hom.app (op U) (a.val (op U)) = 0 := by
    obtain ⟨σ, e, he⟩ := ha U
    let s := (σ.s (e.symm 0)).val (op (Over.mk (𝟙 U)))
    have hs : s.val = a.val (op U) := he (e.symm 0)
    have hm : a.val (op U) ∈
        (ConstantCompletion.kernelIdeal (residue l E X)).sections U := by
      rw [← hs]
      exact s.property
    have hk : (ConstantCompletion.kernelIdeal (residue l E X)).sections U =
        RingHom.ker ((residue l E X).hom.app (op U)).hom :=
      (ConstantCompletion.kernelIdeal_existsUnique (residue l E X)).exists.choose_spec U
    rw [hk] at hm
    exact hm
  obtain ⟨v, hu, hz, ht⟩ := koszul_finite_augmentation l E X a hres P
  let t : (ringedKoszulTensorTower (ring l E X) 1 (fun _ ↦ a)).obj
      (complex l E X P) ⟶ quotients l E X P := NatTrans.ofOpSequence v ht
  let q : ringedKoszulTensorTowerComplex (ring l E X) 1 (fun _ ↦ a)
      (complex l E X P) ⟶ quotientComplex l E X P :=
    { f i := Functor.whiskerRight t
        (HomologicalComplex.eval (ConstantCompletion.Mod (ring l E X)) (.up ℤ) i)
      comm' i j hij := by
        have hj : i + 1 = j := hij
        subst j
        apply NatTrans.ext
        funext n
        simpa only [ringedKoszulTensorTowerComplex, CochainComplex.of_d,
          quotientComplex, HomologicalComplex.functorEquivalence,
          HomologicalComplex.functorEquivalence.inverse, NatTrans.comp_app,
          Functor.whiskerRight_app, Functor.whiskerLeft_app,
          HomologicalComplex.eval_map, HomologicalComplex.dNatTrans_app] using
          (t.app n).comm i (i + 1) }
  refine ⟨q, ?_, ?_⟩
  · apply (HomologicalComplex.quasiIso_iff_evaluation q).2
    intro n
    let ev :=
      ((evaluation ℕᵒᵖ (ConstantCompletion.Mod (ring l E X))).obj n).mapHomologicalComplex
        (.up ℤ)
    let e : ev.obj (ringedKoszulTensorTowerComplex (ring l E X) 1 (fun _ ↦ a)
        (complex l E X P)) ≅
        ((ringedKoszulTensorTower (ring l E X) 1 (fun _ ↦ a)).obj
          (complex l E X P)).obj n :=
      HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
        intro i j hij
        have hj : i + 1 = j := hij
        subst j
        simp [ev, ringedKoszulTensorTowerComplex, CochainComplex.of_d])
    have hv : QuasiIso (t.app n) :=
      koszul_finite_augmentation_quasiIso l E X a ha P hP n.unop
        (v n.unop) (hu n.unop) (hz n.unop)
    have hq : ev.map q = e.hom ≫ t.app n := by
      apply HomologicalComplex.hom_ext
      intro i
      simp [ev, q, e]
    change QuasiIso (ev.map q)
    rw [hq]
    infer_instance
  · apply HomologicalComplex.hom_ext
    intro i
    change limit.lift _ (ringedKoszulTensorUnitCone (ring l E X) 1 (fun _ ↦ a)
        (complex l E X P) i) ≫ limMap
          (Functor.whiskerRight t
            (HomologicalComplex.eval (ConstantCompletion.Mod (ring l E X)) (.up ℤ) i)) =
      limit.lift _ (strictTowerUnitCone (quotients l E X P)
        (complex l E X P) (quotientUnits l E X P) i)
    apply limit.hom_ext
    intro n
    rw [Category.assoc, limMap_π, ← Category.assoc, limit.lift_π, limit.lift_π]
    exact congrArg (fun f ↦ f.f i) (hu n.unop)

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
