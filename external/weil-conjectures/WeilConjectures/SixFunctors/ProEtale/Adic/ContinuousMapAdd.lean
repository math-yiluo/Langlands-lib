/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf

/-!
# Sheaves of continuous maps into topological abelian groups

The additive analogues, for a topological abelian group `M` (not necessarily a ring), of the
sheaves of continuous maps of `WeilConjectures.CategoryTheory.RingObjects.ContinuousMap`:

- `AlgebraicGeometry.ProEtale.continuousMapAddSheaf X M`: the abelian sheaf `U ↦ C(U, M)` on
  `X_proét`, and `continuousMapAddSheafMap` for continuous additive maps;
- `AlgebraicGeometry.ProEtale.constantSheafIsoContinuousMapAddSheaf`: for `M` discrete, it is the
  constant sheaf with value `M`, naturally in `M`
  (`constantSheaf_map_comp_constantSheafIsoContinuousMapAddSheaf_hom`);
- `AlgebraicGeometry.ProEtale.isLimitContinuousMapAddSheafCone`: for a tower of topological
  abelian groups `Qₙ`, `C(-, lim Qₙ)` is the limit of the sheaves `C(-, Qₙ)`, with
  `lim Qₙ = towerLimitAddSubgroup τ`.

This allows towers of stalks which are modules rather than rings, e.g. finitely generated
`𝒪_E`-modules with torsion.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u})

section Add

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- The abelian presheaf `U ↦ C(U, M)` of continuous maps into a topological abelian group `M`
on the small pro-étale site of `X`, lifted to `Type (u + 1)`. -/
noncomputable def continuousMapAddPresheaf : X.ProEtᵒᵖ ⥤ Ab.{u + 1} where
  obj U := AddCommGrpCat.of (ULift.{u + 1} C(U.unop.left, M))
  map f := AddCommGrpCat.ofHom
    { toFun g := ULift.up (g.down.comp f.unop.left.base.hom)
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The presheaf of types underlying `continuousMapAddPresheaf X M` is the restriction of
mathlib's presheaf `U ↦ C(U, M)`. -/
noncomputable def continuousMapAddPresheafForgetIso :
    continuousMapAddPresheaf X M ⋙ forget Ab.{u + 1} ≅
      (ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheaf M ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The presheaf `U ↦ C(U, M)` is a sheaf for the pro-étale topology. -/
lemma isSheaf_continuousMapAddPresheaf :
    Presheaf.IsSheaf (ProEt.topology X) (continuousMapAddPresheaf X M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget Ab.{u + 1}),
    Presheaf.isSheaf_of_iso_iff (continuousMapAddPresheafForgetIso X M)]
  refine Functor.op_comp_isSheaf_of_isSheaf (F := ProEt.forget X ⋙ Over.forget X)
    (J := ProEt.topology X) (K := proetaleTopology) _ ?_
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  exact (isSheaf_fpqcTopology_continuousMapPresheaf M).of_le proetaleTopology_le_fpqcTopology

/-- The abelian sheaf `U ↦ C(U, M)` of continuous maps into a topological abelian group. -/
noncomputable def continuousMapAddSheaf : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  ⟨continuousMapAddPresheaf X M, isSheaf_continuousMapAddPresheaf X M⟩

variable {M} {M' : Type} [TopologicalSpace M'] [AddCommGroup M'] [IsTopologicalAddGroup M']

/-- Postcomposition with a continuous additive map `φ : M →+ M'`. -/
noncomputable def continuousMapAddSheafMap (φ : M →+ M') (hφ : Continuous φ) :
    continuousMapAddSheaf X M ⟶ continuousMapAddSheaf X M' :=
  ⟨{ app U := AddCommGrpCat.ofHom
      { toFun g := ULift.up ((⟨φ, hφ⟩ : C(M, M')).comp g.down)
        map_zero' := by ext; simp
        map_add' _ _ := by ext; simp }
     naturality _ _ _ := rfl }⟩

variable (M)

/-- The constant functions, from the constant abelian presheaf with value `M` to `U ↦ C(U, M)`. -/
noncomputable def constToContinuousMapAddPresheaf :
    (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} M)) ⟶
      continuousMapAddPresheaf X M where
  app _ := AddCommGrpCat.ofHom
    { toFun t := ULift.up (ContinuousMap.const _ t.down)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

variable [DiscreteTopology M]

/-- The constant functions are locally bijective onto the continuous maps to a discrete group. -/
lemma w_constToContinuousMapAddPresheaf :
    (ProEt.topology X).W (constToContinuousMapAddPresheaf X M) := by
  rw [GrothendieckTopology.W_iff_isLocallyBijective]
  refine ⟨⟨fun {U} x y h ↦ ProEt.mem_topology_of_isOpenImmersion U.unop _
    (fun _ : U.unop.left ↦ overOpens (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U.unop ⊤)
    (fun _ ↦ overOpensι (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U.unop ⊤)
    (fun _ ↦ inferInstanceAs (IsOpenImmersion (⊤ : U.unop.left.Opens).ι))
    (fun p ↦ ⟨p, ⟨p, trivial⟩, rfl⟩) fun p ↦ ?_⟩, ⟨fun {U} s ↦ ?_⟩⟩
  · have hxy : x = y := by
      obtain ⟨x⟩ := x
      obtain ⟨y⟩ := y
      have := congrArg (fun z : ULift.{u + 1} C(U.unop.left, M) ↦ z.down p) h
      exact congrArg ULift.up this
    subst hxy
    rfl
  · refine ProEt.mem_topology_of_isOpenImmersion U _
      (fun p : U.left ↦ overOpens (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U
        ⟨s.down ⁻¹' {s.down p}, (isOpen_discrete _).preimage s.down.continuous⟩)
      (fun p ↦ overOpensι (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U _)
      (fun p ↦ inferInstanceAs (IsOpenImmersion (Opens.ι _)))
      (fun p ↦ ⟨p, ⟨p, rfl⟩, rfl⟩) fun p ↦ ⟨ULift.up (s.down p), ?_⟩
    refine congrArg ULift.up (ContinuousMap.ext fun q ↦ ?_)
    exact q.2.symm

/-- **Continuous maps to a discrete abelian group form the constant sheaf.** -/
noncomputable def constantSheafIsoContinuousMapAddSheaf :
    (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} M)) ≅
      continuousMapAddSheaf X M :=
  have := ((ProEt.topology X).W_iff _).1 (w_constToContinuousMapAddPresheaf X M)
  asIso ((presheafToSheaf _ _).map (constToContinuousMapAddPresheaf X M)) ≪≫
    asIso ((sheafificationAdjunction _ _).counit.app (continuousMapAddSheaf X M))

variable {M}

/-- An additive map, as a morphism of the universe lifts. -/
noncomputable def uliftAddMonoidHom (τ : M →+ M') :
    AddCommGrpCat.of (ULift.{u + 1} M) ⟶ AddCommGrpCat.of (ULift.{u + 1} M') :=
  AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    (τ.comp AddEquiv.ulift.toAddMonoidHom))

variable [DiscreteTopology M']

/-- The identification of the constant sheaf with continuous maps to a discrete group is
natural in the group. -/
lemma constantSheaf_map_comp_constantSheafIsoContinuousMapAddSheaf_hom (τ : M →+ M') :
    (constantSheaf (ProEt.topology X) Ab.{u + 1}).map (uliftAddMonoidHom.{u} τ) ≫
        (constantSheafIsoContinuousMapAddSheaf X M').hom =
      (constantSheafIsoContinuousMapAddSheaf X M).hom ≫
        continuousMapAddSheafMap X τ continuous_of_discreteTopology := by
  have hc := (sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).counit.naturality
    (continuousMapAddSheafMap X τ continuous_of_discreteTopology)
  simp only [Functor.comp_map, Functor.id_map] at hc
  simp only [constantSheafIsoContinuousMapAddSheaf, Iso.trans_hom, asIso_hom, Category.assoc]
  refine Eq.trans ?_ (congrArg (fun k ↦ (presheafToSheaf _ _).map
    (constToContinuousMapAddPresheaf X M) ≫ k) hc)
  change (presheafToSheaf _ _).map ((Functor.const _).map (uliftAddMonoidHom τ)) ≫
    (presheafToSheaf _ _).map (constToContinuousMapAddPresheaf X M') ≫ _ = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rfl

end Add

section Limit

variable {Qs : ℕ → Type} [∀ n, TopologicalSpace (Qs n)] [∀ n, AddCommGroup (Qs n)]
  [∀ n, IsTopologicalAddGroup (Qs n)] (τ : ∀ n, Qs (n + 1) →+ Qs n)
  (hτ : ∀ n, Continuous (τ n))

/-- The tower `n ↦ C(-, Qₙ)` of abelian sheaves attached to a tower of topological groups. -/
noncomputable def continuousMapAddSheafTower : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  Functor.ofOpSequence (C := Sheaf (ProEt.topology X) Ab.{u + 1})
    (X := fun n ↦ continuousMapAddSheaf X (Qs n))
    fun n ↦ continuousMapAddSheafMap X (τ n) (hτ n)

/-- The transitions of `continuousMapAddSheafTower`. -/
lemma continuousMapAddSheafTower_map_succ (n : ℕ) :
    (continuousMapAddSheafTower X τ hτ).map (homOfLE (n.le_add_right 1)).op =
      continuousMapAddSheafMap X (τ n) (hτ n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The limit `lim Qₙ` of a tower of topological groups, as the subgroup of compatible
families. -/
def towerLimitAddSubgroup : AddSubgroup (∀ n, Qs n) where
  carrier := {x | ∀ n, τ n (x (n + 1)) = x n}
  add_mem' hx hy n := by simp [map_add, hx n, hy n]
  zero_mem' n := by simp
  neg_mem' hx n := by simp [map_neg, hx n]

/-- The projection `lim Qₙ → Qₙ`. -/
def towerLimitAddSubgroupπ (n : ℕ) : towerLimitAddSubgroup τ →+ Qs n :=
  (Pi.evalAddMonoidHom Qs n).comp (towerLimitAddSubgroup τ).subtype

omit [∀ n, IsTopologicalAddGroup (Qs n)] in
/-- The projections `lim Qₙ → Qₙ` are continuous. -/
lemma continuous_towerLimitAddSubgroupπ (n : ℕ) : Continuous (towerLimitAddSubgroupπ τ n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- The cone `C(-, lim Qₙ) ⟶ C(-, Qₙ)`. -/
noncomputable def continuousMapAddSheafCone :
    Cone (continuousMapAddSheafTower X τ hτ) where
  pt := continuousMapAddSheaf X (towerLimitAddSubgroup τ)
  π := NatTrans.ofOpSequence (fun n ↦ continuousMapAddSheafMap X (towerLimitAddSubgroupπ τ n)
      (continuous_towerLimitAddSubgroupπ τ n)) fun n ↦ by
    refine (Category.id_comp _).trans ?_
    erw [continuousMapAddSheafTower_map_succ]
    ext U f
    exact congrArg ULift.up (ContinuousMap.ext fun x ↦ ((f.down x).2 n).symm)

/-- **`C(-, lim Qₙ)` is the limit of the sheaves `C(-, Qₙ)`** for a tower of topological abelian
groups, `lim Qₙ` carrying the subspace topology of the product. -/
noncomputable def isLimitContinuousMapAddSheafCone :
    IsLimit (continuousMapAddSheafCone X τ hτ) := by
  have : ReflectsLimitsOfShape ℕᵒᵖ (forget Ab.{u + 1}) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  refine isLimitOfReflects (sheafToPresheaf _ _) (evaluationJointlyReflectsLimits _ fun U ↦
    isLimitOfReflects (forget Ab.{u + 1}) ((Types.isLimit_iff _).2 fun s hs ↦ ?_).some)
  have hcompat (y : U.unop.left) (n : ℕ) :
      τ n ((s (op (n + 1))).down y) = (s (op n)).down y := by
    have h := hs (homOfLE (n.le_add_right 1)).op
    simp only [Functor.comp_map] at h
    erw [continuousMapAddSheafTower_map_succ] at h
    exact congrArg (fun g : ULift.{u + 1} C(U.unop.left, Qs n) ↦ g.down y) h
  let x : U.unop.left → towerLimitAddSubgroup τ := fun y ↦
    ⟨fun n ↦ (s (op n)).down y, hcompat y⟩
  have hcont : Continuous x := Continuous.subtype_mk (continuous_pi fun n ↦
    (s (op n)).down.continuous) _
  refine ⟨ULift.up ⟨x, hcont⟩, fun j ↦ ?_, fun z hz ↦ ?_⟩
  · exact congrArg ULift.up (ContinuousMap.ext fun y ↦ rfl)
  · refine congrArg ULift.up (ContinuousMap.ext fun y ↦ Subtype.ext (funext fun n ↦ ?_))
    exact congrArg (fun g : ULift.{u + 1} C(U.unop.left, Qs n) ↦ g.down y) (hz (op n))

end Limit

end AlgebraicGeometry.ProEtale
