/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageHomComparison

/-! # Signed power transport across an isomorphism of sites

The generic internal-Hom argument is separated from its coefficient specializations
so each module can be compiled within the project's time limit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor
namespace WeilConjectures
namespace FrobeniusCoefficientTwists

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleModuleInverseImage MorphismProperty.Over.pullback constantSheaf

section SignedHelpers
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

private theorem ringedPull_hom_ext {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    {M : proEtaleRingModules Y R} {N : proEtaleRingModules X S}
    (a b : (proEtaleRingModulePullback g R S c).obj M ⟶ N)
    (h : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      a.val.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op V) x) =
        b.val.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op V) x)) :
    a = b := by
  apply ((proEtaleRingModuleAdjunction g R S c).homEquiv M N).injective
  ext V x
  exact h V.unop x

section RingedHomProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem ringedUnit_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) :
    IsIso ((proEtaleRingModuleAdjunction g R S c).unit.app M) := by
  let P : proEtaleRingModules Y R ⥤ Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let Q : proEtaleRingModules X S ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
  let a := proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}
  let eta := (proEtaleRingModuleAdjunction g R S c).unit.app M
  let e := (a.homEquiv (P.obj M)
    (Q.obj ((proEtaleRingModulePullback g R S c).obj M))).symm (P.map eta)
  have : IsIso e := AlgebraicGeometry.ProEtale.pullback_unit_mate_isIso.{u} g R S c M
  have : IsIso a.unit :=
    (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} g
      AddCommGrpCat.{u + 1}).2.1
  have he := (a.homEquiv (P.obj M)
    (Q.obj ((proEtaleRingModulePullback g R S c).obj M))).apply_symm_apply (P.map eta)
  erw [Adjunction.homEquiv_unit] at he
  have : IsIso (P.map eta) := by
    erw [← he]
    change IsIso (a.unit.app (P.obj M) ≫
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map e)
    have hu : IsIso (a.unit.app (P.obj M)) := NatIso.isIso_app_of_isIso _ _
    have hm : IsIso ((proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map e) :=
      Functor.map_isIso _ e
    exact IsIso.comp_isIso' hu hm
  exact isIso_of_reflects_iso eta P

private theorem ringedPush_reflects {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    (proEtaleRingModuleDirectImage g R S c).ReflectsIsomorphisms := by
  let : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).IsEquivalence :=
    (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} g
      AddCommGrpCat.{u + 1}).1
  let : (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).IsEquivalence :=
    (proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).isEquivalence_right_of_isEquivalence_left
  have hr : (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).ReflectsIsomorphisms :=
    inferInstance
  exact @PurHom.push_reflects_generic _ _ _ _ (proEtaleBaseChange g)
    (ProEt.topology Y) (ProEt.topology X) _
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    _ hr

private theorem ringedDirect_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    IsIso (proEtaleRingDirectImageMap g R S c) := by
  have : IsIso ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R) :=
    PurHom.ringUnit_iso g R
  change IsIso ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R ≫
    (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map c.hom)
  infer_instance

private def ringedHomIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (M N : proEtaleRingModules Y R) :
    (proEtaleRingModulePullback g R S c).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := S)
        ((proEtaleRingModulePullback g R S c).obj M)
        ((proEtaleRingModulePullback g R S c).obj N) := by
  let : (proEtaleBaseChange g).IsEquivalence := PurHom.baseChange_equivalence g
  let : IsIso (proEtaleRingDirectImageMap g R S c) := ringedDirect_isIso g R S c
  let : (proEtaleRingModuleDirectImage g R S c).ReflectsIsomorphisms :=
    ringedPush_reflects g R S c
  exact @PurHom.comparisonIso _ _ _ _ (proEtaleBaseChange g)
    (PurHom.baseChange_equivalence g) (ProEt.topology Y) (ProEt.topology X) _ _ _
    S R (proEtaleRingDirectImageMap g R S c) (ringedDirect_isIso g R S c)
    (proEtaleRingModulePullback g R S c) (proEtaleRingModuleAdjunction g R S c)
    (ringedUnit_isIso g R S c) (ringedPush_reflects g R S c) M N

end RingedHomProof

section RingedHomUniqueness
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem ringedDual_ext {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (M N : proEtaleRingModules Y R) (M' N' : proEtaleRingModules X S)
    (e : (proEtaleRingModulePullback g R S c).obj M ≅ M')
    (a b : (proEtaleRingModulePullback g R S c).obj
      (SheafOfModules.homObj (R := R) M N) ⟶ SheafOfModules.homObj (R := S) M' N')
    (h : ∀ (V W : Y.ProEt) (f : W ⟶ V)
      (phi : (SheafOfModules.homObj (R := R) M N).val.obj (op V))
      (x : M.val.obj (op W)),
      ((a.val.app (op ((proEtaleBaseChange g).obj V))
        (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) phi)).app
        (op (Over.mk ((proEtaleBaseChange g).map f))))
        (e.hom.val.app (op ((proEtaleBaseChange g).obj W))
          (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op W) x)) =
      ((b.val.app (op ((proEtaleBaseChange g).obj V))
        (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) phi)).app
        (op (Over.mk ((proEtaleBaseChange g).map f))))
        (e.hom.val.app (op ((proEtaleBaseChange g).obj W))
          (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op W) x))) : a = b := by
  let B := proEtaleBaseChange g
  let : B.IsEquivalence := PurHom.baseChange_equivalence g
  apply ((proEtaleRingModuleAdjunction g R S c).homEquiv _ _).injective
  ext V phi
  let H := Over.post (X := V.unop) B
  let Q := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj H.op
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply Q.map_injective
  ext W z
  have : IsIso ((proEtaleRingModuleAdjunction g R S c).unit.app M) :=
    ringedUnit_isIso g R S c M
  have : IsIso (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app
      (op W.unop.left)) :=
    (SheafOfModules.evaluation _ (op W.unop.left)).map_isIso
      ((proEtaleRingModuleAdjunction g R S c).unit.app M)
  have : IsIso (e.hom.val.app (op (B.obj W.unop.left))) :=
    (SheafOfModules.evaluation _ (op (B.obj W.unop.left))).map_isIso e.hom
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (e.hom.val.app (op (B.obj W.unop.left)))).2 z
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app
      (op W.unop.left))).2 y
  exact h V.unop W.unop.left W.unop.hom phi x

end RingedHomUniqueness

section RingedHomFormula
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem ringedHomIso_section {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (M N : proEtaleRingModules Y R) (V W : Y.ProEt) (a : W ⟶ V)
    (phi : (SheafOfModules.homObj (R := R) M N).val.obj (op V))
    (x : M.val.obj (op W)) :
    (((ringedHomIso g R S c M N).hom.val.app (op ((proEtaleBaseChange g).obj V))
      (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) phi)).app
        (op (Over.mk ((proEtaleBaseChange g).map a))))
      (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op W) x) =
    ((proEtaleRingModuleAdjunction g R S c).unit.app N).val.app (op W)
      (phi.app (op (Over.mk a)) x) := by
  let : (proEtaleBaseChange g).IsEquivalence := PurHom.baseChange_equivalence g
  let : IsIso (proEtaleRingDirectImageMap g R S c) := ringedDirect_isIso g R S c
  let : (proEtaleRingModuleDirectImage g R S c).ReflectsIsomorphisms :=
    ringedPush_reflects g R S c
  unfold ringedHomIso
  have hsec (A : proEtaleRingModules Y R) (U : Y.ProEt)
      (z : A.val.obj (op U)) :
      (PurHom.unitIso (proEtaleBaseChange g) (ProEt.topology Y) (ProEt.topology X)
        S R (proEtaleRingDirectImageMap g R S c)
        (proEtaleRingModulePullback g R S c) (proEtaleRingModuleAdjunction g R S c)
        (ringedUnit_isIso g R S c) A).hom.val.app (op U) z =
      ((proEtaleRingModuleAdjunction g R S c).unit.app A).val.app (op U) z := by
    erw [PurHom.unitIso_hom (proEtaleBaseChange g) (ProEt.topology Y) (ProEt.topology X)
      S R (proEtaleRingDirectImageMap g R S c)
      (proEtaleRingModulePullback g R S c) (proEtaleRingModuleAdjunction g R S c)
      (ringedUnit_isIso g R S c) A]
    rfl
  have h := @PurHom.comparisonIso_section _ _ _ _ (proEtaleBaseChange g)
      (PurHom.baseChange_equivalence g) (ProEt.topology Y) (ProEt.topology X) _ _ _
      S R (proEtaleRingDirectImageMap g R S c) (ringedDirect_isIso g R S c)
      (proEtaleRingModulePullback g R S c) (proEtaleRingModuleAdjunction g R S c)
      (ringedUnit_isIso g R S c) (ringedPush_reflects g R S c) M N V W a phi x
  have h' := h.trans (hsec N W (phi.app (op (Over.mk a)) x))
  simpa only [hsec] using h'

end RingedHomFormula

section RingedDualProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private def ringedDualMap {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (M N : proEtaleRingModules Y R) (M' N' : proEtaleRingModules X S)
    (e : (proEtaleRingModulePullback g R S c).obj M ≅ M')
    (f : (proEtaleRingModulePullback g R S c).obj N ≅ N') :
    (proEtaleRingModulePullback g R S c).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := S) M' N' :=
  ringedHomIso g R S c M N ≪≫ PurHom.homCongr S e f

private theorem ringedDualMap_section {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (M N : proEtaleRingModules Y R) (M' N' : proEtaleRingModules X S)
    (e : (proEtaleRingModulePullback g R S c).obj M ≅ M')
    (f : (proEtaleRingModulePullback g R S c).obj N ≅ N')
    (V W : Y.ProEt) (a : W ⟶ V)
    (phi : (SheafOfModules.homObj (R := R) M N).val.obj (op V))
    (x : M.val.obj (op W)) :
    (((ringedDualMap g R S c M N M' N' e f).hom.val.app
      (op ((proEtaleBaseChange g).obj V))
      (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) phi)).app
        (op (Over.mk ((proEtaleBaseChange g).map a))))
      (e.hom.val.app (op ((proEtaleBaseChange g).obj W))
        (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op W) x)) =
    f.hom.val.app (op ((proEtaleBaseChange g).obj W))
      (((proEtaleRingModuleAdjunction g R S c).unit.app N).val.app (op W)
        (phi.app (op (Over.mk a)) x)) := by
  change f.hom.val.app _
      ((((ringedHomIso g R S c M N).hom.val.app _
        (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) phi)).app
            (op (Over.mk ((proEtaleBaseChange g).map a))))
          (e.inv.val.app (op ((proEtaleBaseChange g).obj W))
            (e.hom.val.app (op ((proEtaleBaseChange g).obj W))
            (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op W) x)))) = _
  have hi := congrArg (fun k ↦ k.val.app (op ((proEtaleBaseChange g).obj W))
    (((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op W) x)) e.hom_inv_id
  change e.inv.val.app _ (e.hom.val.app _ _) =
    ((proEtaleRingModuleAdjunction g R S c).unit.app M).val.app (op W) x at hi
  erw [hi]
  exact congrArg (fun z ↦ f.hom.val.app (op ((proEtaleBaseChange g).obj W)) z)
    (ringedHomIso_section g R S c M N V W a phi x)

end RingedDualProof

section SignedComparisonProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] ringedHomIso ringedDualMap

/-- A comparison on nonnegative powers extends uniquely to the signed powers by
conjugating the internal dual. Source: coefficient-twist clause 3 and Stacks, Tag 03EL.
(blueprint: lem-weil-frobenius-signed-power-transport).
Proof: inverse image at a scheme isomorphism is an equivalence. Its module adjunction
therefore has invertible unit and reflects isomorphisms. Transport internal Hom through
this equivalence and conjugate by the given positive and coefficient comparisons.
Evaluation proves the specified formula. Its uniqueness follows by the adjunction and
extensionality of internal Hom after restriction to every object of the slice site.
Positive and negative integers are disjoint cases, so the maps assemble uniquely. -/
theorem genericSignedProof {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) (N : proEtaleRingModules X S)
    (P : ∀ d : ℕ, (proEtaleRingModulePullback g R S c).obj
      (coefficientTwistPower Y (R := R) M d) ≅ coefficientTwistPower X (R := S) N d) :
    ∃! tau : ∀ m : ℤ, (proEtaleRingModulePullback g R S c).obj
        (coefficientTwistLine Y (R := R) M m) ≅ coefficientTwistLine X (R := S) N m,
      (∀ d : ℕ, HEq (tau (d : ℤ)) (P d)) ∧
      ∀ (n : ℕ) (V W : Y.ProEt) (a : W ⟶ V)
        (phi : (coefficientTwistLine Y (R := R) M (Int.negSucc n)).val.obj (op V))
        (x : (coefficientTwistPower Y (R := R) M (n + 1)).val.obj (op W)),
        ((tau (Int.negSucc n)).hom.val.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op V) phi)).app
            (op (Over.mk ((proEtaleBaseChange g).map a)))
              ((P (n + 1)).hom.val.app (op ((proEtaleBaseChange g).obj W))
                (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op W) x)) =
          (P 0).hom.val.app (op ((proEtaleBaseChange g).obj W))
            (((proEtaleRingModuleAdjunction g R S c).unit.app _).val.app (op W)
              (phi.app (op (Over.mk a)) x)) := by
  let D (n : ℕ) := ringedDualMap g R S c
    (coefficientTwistPower Y (R := R) M (n + 1)) (coefficientTwistPower Y (R := R) M 0)
    (coefficientTwistPower X (R := S) N (n + 1)) (coefficientTwistPower X (R := S) N 0)
    (P (n + 1)) (P 0)
  let tau : ∀ m : ℤ, (proEtaleRingModulePullback g R S c).obj
      (coefficientTwistLine Y (R := R) M m) ≅ coefficientTwistLine X (R := S) N m :=
    fun m ↦ match m with
    | .ofNat n => P n
    | .negSucc n => D n
  refine ⟨tau, ⟨fun _ ↦ HEq.rfl, ?_⟩, ?_⟩
  · intro n V W a phi x
    exact ringedDualMap_section g R S c _ _ _ _ (P (n + 1)) (P 0) V W a phi x
  · intro other hother
    funext m
    cases m with
    | ofNat n => exact eq_of_heq (hother.1 n)
    | negSucc n =>
      apply Iso.ext
      apply ringedDual_ext g R S c _ _ _ _ (P (n + 1))
      intro V W a phi x
      exact (hother.2 n V W a phi x).trans
        (ringedDualMap_section g R S c _ _ _ _ (P (n + 1)) (P 0)
          V W a phi x).symm

end SignedComparisonProof

end SignedHelpers

end FrobeniusCoefficientTwists
end WeilConjectures
