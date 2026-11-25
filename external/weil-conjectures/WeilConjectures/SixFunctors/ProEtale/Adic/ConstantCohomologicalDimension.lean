/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProfiniteCoefficientCohomology
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology

/-!
# Cohomological dimension of the constant `ℓ`-adic sheaf

Let `S` be a scheme of finite type and of dimension at most `d` over a separably closed field.
The pro-étale cohomology `Hᵠ(S_proét, ℚ̄_ℓ)` of the constant `ℓ`-adic sheaf vanishes for `q > 2d`.

The underlying abelian sheaf of `ℚ̄_ℓ,S` is the filtered union of the subsheaves `C(-, Λ)`, for
`Λ` running over the compact subgroups of `ℚ̄_ℓ` spanning a finite-dimensional `ℚ_ℓ`-subspace
(e.g. `ℓ⁻ⁿ 𝒪_E` for finite extensions `E` of `ℚ_ℓ`): over a quasi-compact `U` a locally finite
function has compact image in a finite-dimensional subspace, hence in such a `Λ`. Each `Λ` is
profinite, so `Hᵠ(S_proét, C(-, Λ)) = 0` for `q > 2d`
(`AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_profinite`), and pro-étale
cohomology of the qcqs scheme `S` commutes with filtered colimits
(`AlgebraicGeometry.Scheme.ProEt.subsingleton_H_of_isColimit_of_isFiltered`). Finally the
cohomology of `ℚ̄_ℓ,S` as a sheaf of `ℚ̄_ℓ`-modules is that of its underlying abelian sheaf
(`AlgebraicGeometry.ProEtale.forgetRightDerivedGlobalSectionsIso`).

## Main statements

- `PadicAlgCl.CompactLattice`: the directed set of compact subgroups of `ℚ̄_ℓ` with
  finite-dimensional `ℚ_ℓ`-span.
- `AlgebraicGeometry.ProEtale.isColimitAdicConstantSheafCocone`: the underlying abelian sheaf of
  `ℚ̄_ℓ,S` is the colimit of the sheaves `C(-, Λ)`.
- `AlgebraicGeometry.ProEtale.isZero_rightDerived_Γ_adicConstantSheaf_of_two_mul_lt`: the
  vanishing of `Hᵠ(S_proét, ℚ̄_ℓ)` for `q > 2d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime]

/-- The compact additive subgroups of `ℚ̄_ℓ` whose `ℚ_ℓ`-span is finite-dimensional, ordered by
inclusion. -/
abbrev CompactLattice : Type :=
  {Λ : AddSubgroup (PadicAlgCl l) // IsCompact (Λ : Set (PadicAlgCl l)) ∧
    FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (Λ : Set (PadicAlgCl l)))}

instance CompactLattice.isDirected : IsDirected (CompactLattice l) (· ≤ ·) where
  directed Λ Λ' := by
    refine ⟨⟨Λ.1 ⊔ Λ'.1, ?_, ?_⟩, le_sup_left (a := Λ.1), le_sup_right (a := Λ.1)⟩
    · rw [AddSubgroup.add_normal]
      exact Λ.2.1.add Λ'.2.1
    · have := Λ.2.2
      have := Λ'.2.2
      refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l] (Λ.1 : Set _) ⊔
        Submodule.span ℚ_[l] (Λ'.1 : Set _)) (Submodule.span_le.2 ?_)
      rw [AddSubgroup.add_normal]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact Submodule.add_mem_sup (Submodule.subset_span hx) (Submodule.subset_span hy)

instance : Nonempty (CompactLattice l) :=
  ⟨⟨⊥, by simp, by
    refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    simp⟩⟩

variable {l}

/-- A compact subset of `ℚ̄_ℓ` spanning a finite-dimensional `ℚ_ℓ`-subspace `E` lies in a compact
subgroup with finite-dimensional span: a closed ball of `E`, a subgroup since the norm is
ultrametric and compact since `E` is a finite-dimensional normed space over `ℚ_ℓ`. -/
lemma exists_compactLattice_of_isCompact {K : Set (PadicAlgCl l)} (hK : IsCompact K)
    (hKf : FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] K)) :
    ∃ Λ : CompactLattice l, K ⊆ Λ.1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set E := Submodule.span ℚ_[l] K
  let Λ : AddSubgroup (PadicAlgCl l) :=
    { carrier := {x | x ∈ E ∧ ‖x‖ ≤ max R 0}
      add_mem' := fun ha hb ↦ ⟨E.add_mem ha.1 hb.1,
        (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.2 hb.2)⟩
      zero_mem' := ⟨E.zero_mem, by simp⟩
      neg_mem' := fun ha ↦ ⟨E.neg_mem ha.1, by simpa using ha.2⟩ }
  have hΛ : (Λ : Set (PadicAlgCl l)) = Subtype.val '' Metric.closedBall (0 : E) (max R 0) := by
    ext x
    simp [Λ, and_comm]
  have : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
  refine ⟨⟨Λ, ?_, Submodule.finiteDimensional_of_le (S₂ := E) (Submodule.span_le.2 ?_)⟩, ?_⟩
  · rw [hΛ]
    exact (isCompact_closedBall _ _).image continuous_subtype_val
  · exact fun x hx ↦ hx.1
  · exact fun x hx ↦ ⟨Submodule.subset_span hx, (hR x hx).trans (le_max_left _ _)⟩

/-- The decreasing sequence of open subgroups `{x ∈ Λ | ‖x‖ < 1 / (m + 1)}` of a compact
lattice. -/
noncomputable def CompactLattice.ballSubgroup (Λ : CompactLattice l) (m : ℕ) :
    OpenAddSubgroup Λ.1 :=
  IsUltrametricDist.ball_openAddSubgroup (S := Λ.1) (r := 1 / ((m : ℝ) + 1)) (by positivity)

lemma CompactLattice.ballSubgroup_succ_le (Λ : CompactLattice l) (m : ℕ) :
    Λ.ballSubgroup (m + 1) ≤ Λ.ballSubgroup m := by
  intro x hx
  refine Metric.mem_ball.2 (lt_of_lt_of_le (Metric.mem_ball.1 hx) ?_)
  gcongr
  linarith

lemma CompactLattice.eq_zero_of_forall_mem_ballSubgroup (Λ : CompactLattice l) (x : Λ.1)
    (hx : ∀ m, x ∈ Λ.ballSubgroup m) : x = 0 := by
  rw [← dist_eq_zero]
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε ↦ ?_) dist_nonneg
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  exact (Metric.mem_ball.1 (hx m)).trans (by simpa using hm)

instance (Λ : CompactLattice l) : CompactSpace Λ.1 :=
  isCompact_iff_compactSpace.1 Λ.2.1

/-- A continuous function with values in a compact lattice is locally finite. -/
noncomputable def CompactLattice.functionsHom (Λ : CompactLattice l) (T : Type*)
    [TopologicalSpace T] : C(T, Λ.1) →+ locallyFiniteFunctions l T where
  toFun f := ⟨⟨fun t ↦ (f t : PadicAlgCl l), continuous_subtype_val.comp f.continuous⟩, by
    have := Λ.2.2
    refine mem_locallyFiniteFunctions_of_finiteDimensional
      (Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l] (Λ.1 : Set _))
        (Submodule.span_mono ?_))
    rintro _ ⟨t, rfl⟩
    exact (f t).2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u})

instance : IsDirected (ULift.{u + 1} (CompactLattice l)) (· ≤ ·) where
  directed Λ Λ' := by
    obtain ⟨M, h, h'⟩ := (CompactLattice.isDirected l).directed Λ.down Λ'.down
    exact ⟨⟨M⟩, h, h'⟩

/-- The diagram `Λ ↦ C(-, Λ)` of abelian sheaves on `S_proét`, indexed by the compact lattices
of `ℚ̄_ℓ`. -/
noncomputable def compactLatticeDiagram :
    ULift.{u + 1} (CompactLattice l) ⥤ Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} where
  obj Λ := continuousSheaf S Λ.down.1
  map {Λ Λ'} f := continuousSheafMap S
    ⟨AddSubgroup.inclusion (show Λ.down.1 ≤ Λ'.down.1 from (leOfHom f : Λ ≤ Λ')),
      continuous_subtype_val.subtype_mk _⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying abelian sheaf of the constant `ℓ`-adic sheaf `ℚ̄_ℓ,S`. -/
noncomputable abbrev adicConstantSheafAb : Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} :=
  (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) S).obj (adicConstantSheaf l S)

/-- The inclusion `C(-, Λ) ⟶ ℚ̄_ℓ,S` of abelian sheaves. -/
noncomputable def compactLatticeToAdicConstantSheaf (Λ : CompactLattice l) :
    continuousSheaf S Λ.1 ⟶ adicConstantSheafAb l S :=
  ⟨{ app V := AddCommGrpCat.ofHom
        { toFun f := ULift.up (Λ.functionsHom V.unop.left (ULift.down f))
          map_zero' := rfl
          map_add' _ _ := rfl }
     naturality _ _ _ := rfl }⟩

/-- The cocone of the inclusions `C(-, Λ) ⟶ ℚ̄_ℓ,S`. -/
noncomputable def adicConstantSheafCocone : Cocone (compactLatticeDiagram l S) where
  pt := adicConstantSheafAb l S
  ι := { app Λ := compactLatticeToAdicConstantSheaf l S Λ.down
         naturality _ _ _ := rfl }

instance (Λ : CompactLattice l) : Mono (compactLatticeToAdicConstantSheaf l S Λ) := by
  have (V : (Scheme.ProEt S)ᵒᵖ) :
      Mono (((sheafToPresheaf _ _).map (compactLatticeToAdicConstantSheaf l S Λ)).app V) := by
    refine (AddCommGrpCat.mono_iff_injective _).2 fun x y h ↦ ?_
    have h' := congrArg (fun z : ULift.{u + 1} (locallyFiniteFunctions l V.unop.left) ↦
      (z.down : C(V.unop.left, PadicAlgCl l))) h
    exact ULift.ext (ContinuousMap.ext fun t ↦ Subtype.ext (DFunLike.congr_fun h' t))
  have : Mono ((sheafToPresheaf _ _).map (compactLatticeToAdicConstantSheaf l S Λ)) :=
    NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

/-- Every section of `ℚ̄_ℓ,S` comes locally from some `C(-, Λ)`: on an affine open `W` the
section has compact image spanning a finite-dimensional subspace, which lies in a compact
lattice. -/
lemma epi_colimitDesc_adicConstantSheafCocone :
    Epi (colimit.desc (compactLatticeDiagram l S) (adicConstantSheafCocone l S)) := by
  rw [← Sheaf.isLocallySurjective_iff_epi']
  refine ⟨fun {V} s ↦ ?_⟩
  let s' : ULift.{u + 1} (locallyFiniteFunctions l V.left) := s
  refine Scheme.ProEt.mem_topology_of_openImmersion _ (fun x : V.left ↦ V.left.affineCover.f x)
    (fun x ↦ ?_) fun x ↦ ?_
  · obtain ⟨i, y, rfl⟩ := V.left.affineCover.exists_eq x
    exact ⟨i, y, rfl⟩
  let g : C(V.left.affineCover.X x, PadicAlgCl l) :=
    (s'.down : C(V.left, PadicAlgCl l)).comp (V.left.affineCover.f x).base.hom
  have hg : g ∈ locallyFiniteFunctions l (V.left.affineCover.X x) :=
    comp_mem_locallyFiniteFunctions s'.down.2 _
  obtain ⟨Λ, hΛ⟩ := exists_compactLattice_of_isCompact (isCompact_range g.continuous)
    (finiteDimensional_span_range_of_mem_locallyFiniteFunctions hg)
  let t₀ : C(V.left.affineCover.X x, Λ.1) := ⟨fun w ↦ ⟨g w, hΛ ⟨w, rfl⟩⟩, g.continuous.subtype_mk _⟩
  refine ⟨(colimit.ι (compactLatticeDiagram l S) ⟨Λ⟩).hom.app
    (op (V.ofOpenImmersion (V.left.affineCover.f x))) (ULift.up t₀), ?_⟩
  have h := congrArg (fun φ : continuousSheaf S Λ.1 ⟶ adicConstantSheafAb l S ↦
    φ.hom.app (op (V.ofOpenImmersion (V.left.affineCover.f x))) (ULift.up t₀))
    (colimit.ι_desc (adicConstantSheafCocone l S) ⟨Λ⟩)
  refine h.trans ?_
  rfl

attribute [local instance] IsFiltered.isConnected in
/-- **`ℚ̄_ℓ,S` is the filtered union of the `C(-, Λ)`.** The underlying abelian sheaf of the
constant `ℓ`-adic sheaf is the colimit of the sheaves `C(-, Λ)` over the compact lattices `Λ`
of `ℚ̄_ℓ`. -/
noncomputable def isColimitAdicConstantSheafCocone : IsColimit (adicConstantSheafCocone l S) := by
  have := epi_colimitDesc_adicConstantSheafCocone l S
  have (Λ : ULift.{u + 1} (CompactLattice l)) : Mono ((adicConstantSheafCocone l S).ι.app Λ) :=
    inferInstanceAs (Mono (compactLatticeToAdicConstantSheaf l S Λ.down))
  have : Mono (adicConstantSheafCocone l S).ι := NatTrans.mono_of_mono_app _
  have : Mono (colimit.desc (compactLatticeDiagram l S) (adicConstantSheafCocone l S)) :=
    colim.map_mono' (adicConstantSheafCocone l S).ι (colimit.isColimit _)
      (isColimitConstCocone _ _) _ (by simp)
  have :=
    isIso_of_mono_of_epi (colimit.desc (compactLatticeDiagram l S) (adicConstantSheafCocone l S))
  have : IsIso ((colimit.isColimit _).desc (adicConstantSheafCocone l S)) := this
  exact IsColimit.ofPointIso (colimit.isColimit _)

variable {l S}

/-- The underlying abelian sheaf of `ℚ̄_ℓ,S` has no cohomology above `2d`, for `S` of finite type
and dimension at most `d` over a separably closed field: it is the filtered colimit of the
sheaves `C(-, Λ)`, which have no cohomology above `2d`. -/
theorem subsingleton_H_adicConstantSheafAb_of_two_mul_lt {K : Type u} [Field K] [IsSepClosed K]
    (a : S ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (q : ℕ) (hq : 2 * d < q) :
    Subsingleton (Sheaf.H (adicConstantSheafAb l S) q) := by
  have := LocallyOfFiniteType.isLocallyNoetherian a
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian S := {}
  exact Scheme.ProEt.subsingleton_H_of_isColimit_of_isFiltered S
    (isColimitAdicConstantSheafCocone l S) q fun Λ ↦
      subsingleton_H_continuousSheaf_of_profinite a d hS Λ.down.ballSubgroup
        Λ.down.ballSubgroup_succ_le Λ.down.eq_zero_of_forall_mem_ballSubgroup q hq

instance : IsAddTorsionFree (ULift.{u + 1} (PadicAlgCl l)) where
  eq_of_nsmul_eq_nsmul_of_addCommute _ hn _ _ _ h :=
    ULift.ext (nsmul_right_injective hn (congrArg ULift.down h))

/-- **Cohomological dimension of `ℚ̄_ℓ`.** For a scheme `S` of finite type and of dimension at
most `d` over a separably closed field, `Hᵠ(S_proét, ℚ̄_ℓ) = 0` for `q > 2d`, cohomology being
computed in sheaves of `ℚ̄_ℓ`-modules. -/
theorem isZero_rightDerived_Γ_adicConstantSheaf_of_two_mul_lt {K : Type u} [Field K]
    [IsSepClosed K] (a : S ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (q : ℕ) (hq : 2 * d < q) :
    IsZero (((Sheaf.Γ (Scheme.ProEt.topology S) (WeilCoefficients.{u} l)).rightDerived q).obj
      (adicConstantSheaf l S)) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by lia⟩
  have hH := subsingleton_H_adicConstantSheafAb_of_two_mul_lt (l := l) a d hS (q + 1) hq
  obtain ⟨e₁⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    (Scheme.ProEt.topology S) _ (Scheme.ProEt.isTerminalMkId S) (adicConstantSheafAb l S) q
  let e₂ := forgetRightDerivedGlobalSectionsIso (ULift.{u + 1} (PadicAlgCl l)) S
    (adicConstantSheaf l S) (q + 1)
  have : Subsingleton ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)))
      AddCommGrpCat.{u + 1}).obj (((globalSectionsFunctor (ModuleCat.{u + 1}
        (ULift.{u + 1} (PadicAlgCl l))) S).rightDerived (q + 1)).obj (adicConstantSheaf l S))) :=
    (e₂.addCommGroupIsoToAddEquiv.trans e₁.symm).toEquiv.subsingleton
  have : ((sheafSections (Scheme.ProEt.topology S) (WeilCoefficients.{u} l)).obj
      (op (Scheme.ProEt.mk (𝟙 S)))).Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  refine IsZero.of_iso (ModuleCat.isZero_of_subsingleton (((globalSectionsFunctor (ModuleCat.{u + 1}
    (ULift.{u + 1} (PadicAlgCl l))) S).rightDerived (q + 1)).obj (adicConstantSheaf l S)))
    (Functor.rightDerivedObjIsoOfIso (Sheaf.ΓNatIsoSheafSections _ _
      (Scheme.ProEt.isTerminalMkId S)) (q + 1) _)

end AlgebraicGeometry.ProEtale
