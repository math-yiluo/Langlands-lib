/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.GaloisDescentTrace
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# The trace of a Galois covering on pro-étale sheaves

Let `g : Y ⟶ X` be a quasi-compact surjective weakly étale morphism (for instance a finite étale
covering) and `ρ : Γ → (Y ⟶ Y)` an action of a finite group `Γ` by automorphisms over `X` which is
*Galois*: two morphisms `a b : T ⟶ Y` with `a ≫ g = b ≫ g` agree, locally on `T`, up to one of the
`ρ i` (`AlgebraicGeometry.ProEtale.IsGaloisAction`; equivalently `Y ×_X Y` is covered by the
graphs of the `ρ i`). For an abelian pro-étale sheaf `H` on `X`, the sections of
`g_* g^* H` over `V` are the sections of `H` over `V ×_X Y`, and `Γ` acts on them.

The unit `u : H ⟶ g_* g^* H` is the inclusion of the `Γ`-invariants, and the norm factors through
it: this is the *trace* `t : g_* g^* H ⟶ H` (`AlgebraicGeometry.ProEtale.galoisTrace`), natural in
`H`, with

* `u ≫ t = |Γ| • 𝟙` (`AlgebraicGeometry.ProEtale.unit_comp_galoisTrace`),
* `t ≫ u = ∑ i, ρ i` (`AlgebraicGeometry.ProEtale.galoisTrace_comp_unit`).

So for `|Γ|` invertible on `H` (a `p`-group and `ℤ[1/p]`-linear coefficients) the unit is a split
monomorphism, split by the normalized trace `|Γ|⁻¹ t`, whose idempotent is the average of the
action (`CategoryTheory.comp_normalizedTrace`, `CategoryTheory.nsmul_normalizedTrace_comp_eq_sum`).
This is the finite-level input of the averaging argument over a pro-`p` group (SGA 4½,
[Th. finitude], §3; blueprint `prose-E-10`, `lemma-duality-invariants-pro-p--1`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme Presheaf

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]

@[simp]
private lemma overHomMk_left {A B : X.ProEt} (f : A.left ⟶ B.left) (w : f ≫ B.hom = A.hom)
    (hf : (⊤ : MorphismProperty Scheme.{u}) f) : (MorphismProperty.Over.homMk f w hf).left = f :=
  rfl

@[simp]
private lemma proEtComp_left {A B C : X.ProEt} (f : A ⟶ B) (h : B ⟶ C) :
    (f ≫ h).left = f.left ≫ h.left :=
  rfl

/-- The base change endofunctor `V ↦ V ×_X Y` of the pro-étale site of `X`. -/
noncomputable abbrev baseChangeFunctor : X.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ g ⋙
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)

/-- The projection `V ×_X Y ⟶ V`, the counit of the adjunction between localization and base
change. -/
noncomputable abbrev baseChangeProj : baseChangeFunctor g ⟶ 𝟭 X.ProEt :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g inferInstance trivial).counit

/-- The action `V ×_X Y ⟶ V ×_X Y` of an endomorphism `s` of `Y` over `X`. -/
noncomputable def baseChangeAction (s : Y ⟶ Y) (hs : s ≫ g = g) :
    baseChangeFunctor g ⟶ baseChangeFunctor g where
  app V := MorphismProperty.Over.homMk
    (pullback.map V.hom g V.hom g (𝟙 _) s (𝟙 _) (by simp) (by simp [hs]))
    (by simp [hs]) trivial
  naturality V W f := by
    refine MorphismProperty.Over.Hom.ext ?_
    apply pullback.hom_ext <;> simp

@[reassoc (attr := simp)]
lemma baseChangeAction_app_left_fst (s : Y ⟶ Y) (hs : s ≫ g = g) (V : X.ProEt) :
    ((baseChangeAction g s hs).app V).left ≫ pullback.fst V.hom g = pullback.fst V.hom g := by
  simp [baseChangeAction]

@[reassoc (attr := simp)]
lemma baseChangeAction_app_left_snd (s : Y ⟶ Y) (hs : s ≫ g = g) (V : X.ProEt) :
    ((baseChangeAction g s hs).app V).left ≫ pullback.snd V.hom g = pullback.snd V.hom g ≫ s := by
  simp [baseChangeAction]

lemma baseChangeAction_comp_proj (s : Y ⟶ Y) (hs : s ≫ g = g) :
    baseChangeAction g s hs ≫ baseChangeProj g = baseChangeProj g := by
  refine NatTrans.ext (funext fun V ↦ MorphismProperty.Over.Hom.ext ?_)
  simp

lemma baseChangeAction_comp (s s' : Y ⟶ Y) (hs : s ≫ g = g) (hs' : s' ≫ g = g) :
    baseChangeAction g s hs ≫ baseChangeAction g s' hs' =
      baseChangeAction g (s ≫ s') (by rw [assoc, hs', hs]) := by
  refine NatTrans.ext (funext fun V ↦ MorphismProperty.Over.Hom.ext ?_)
  apply pullback.hom_ext <;> simp

/-- An action `ρ` of `Γ` on `Y` over `X` is *Galois* if two morphisms `a b : T ⟶ Y` with
`a ≫ g = b ≫ g` agree, on the members of an open cover of `T`, up to one of the `ρ i`: the graphs
of the `ρ i` cover `Y ×_X Y`. -/
def IsGaloisAction {Γ : Type u} (ρ : Γ → (Y ⟶ Y)) : Prop :=
  ∀ (T : Scheme.{u}) (a b : T ⟶ Y), a ≫ g = b ≫ g →
    ∃ U : Γ → T.Opens, (∀ x, ∃ i, x ∈ U i) ∧ ∀ i, (U i).ι ≫ b = (U i).ι ≫ a ≫ ρ i

variable [Surjective g] [QuasiCompact g]

/-- The projections `V ×_X Y ⟶ V` are pro-étale coverings. -/
lemma generate_singleton_baseChangeProj_mem (V : X.ProEt) :
    Sieve.generate (Presieve.singleton ((baseChangeProj g).app V)) ∈ ProEt.topology X V := by
  rw [ProEt.mem_topology_iff]
  refine ⟨_, ?_, Sieve.le_generate _⟩
  rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
  change Presieve.singleton (pullback.fst V.hom g) ∈ _
  exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale)
    (inferInstanceAs (WeaklyEtale (pullback.fst V.hom g)))

variable {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)

omit [Surjective g] [QuasiCompact g] in
include hρ in
/-- A Galois action is Galois on every base change `V ×_X Y`. -/
lemma isGalois_baseChangeAction (hgal : IsGaloisAction g ρ) (V T : X.ProEt)
    (a b : T ⟶ (baseChangeFunctor g).obj V)
    (hab : a ≫ (baseChangeProj g).app V = b ≫ (baseChangeProj g).app V) :
    ∃ S ∈ ProEt.topology X T, ∀ ⦃Z : X.ProEt⦄ (c : Z ⟶ T), S c →
      ∃ i, c ≫ b = c ≫ a ≫ (baseChangeAction g (ρ i) (hρ i)).app V := by
  have hab' : a.left ≫ pullback.fst V.hom g = b.left ≫ pullback.fst V.hom g :=
    congrArg (fun f ↦ f.left) hab
  obtain ⟨U, hU, hUρ⟩ := hgal T.left (a.left ≫ pullback.snd V.hom g)
    (b.left ≫ pullback.snd V.hom g) (by
      have ha := MorphismProperty.Over.w a
      have hb := MorphismProperty.Over.w b
      simp only [baseChangeFunctor, Functor.comp_obj, MorphismProperty.Over.map_obj_hom,
        MorphismProperty.Over.pullback_obj_hom] at ha hb
      rw [assoc, assoc, ha, hb])
  let S : Sieve T :=
    { arrows Z c := ∃ i, c ≫ b = c ≫ a ≫ (baseChangeAction g (ρ i) (hρ i)).app V
      downward_closed {Z W} c := by
        rintro ⟨i, hi⟩ e
        exact ⟨i, by rw [assoc, hi, assoc]⟩ }
  refine ⟨S, ProEt.mem_topology_of_openImmersion S (fun i ↦ (U i).ι)
    (fun x ↦ ?_) fun i ↦ ⟨i, ?_⟩, fun Z c hc ↦ hc⟩
  · obtain ⟨i, hi⟩ := hU x
    exact ⟨i, by rw [Opens.range_ι]; exact hi⟩
  · refine MorphismProperty.Over.Hom.ext ?_
    apply pullback.hom_ext
    · simp only [proEtComp_left, ProEt.ofOpenImmersionHom,
        overHomMk_left, assoc, baseChangeAction_app_left_fst]
      rw [hab']
    · simp only [proEtComp_left, ProEt.ofOpenImmersionHom,
        overHomMk_left, assoc, baseChangeAction_app_left_snd]
      simpa only [assoc] using hUρ i



section Trace

variable [Group Γ] [Fintype Γ] (hmul : ∀ a b, ρ a ≫ ρ b = ρ (a * b)) (hgal : IsGaloisAction g ρ)

/-- An abelian pro-étale sheaf is a sheaf of sets after forgetting the group structure. -/
lemma isSheaf_comp_forget (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    Presieve.IsSheaf (ProEt.topology X) (H.obj ⋙ forget AddCommGrpCat.{u + 1}) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose _ (forget _)).obj H).property

include hmul in
omit [Surjective g] [QuasiCompact g] [Fintype Γ] in
lemma baseChangeAction_comp_mul (a b : Γ) :
    baseChangeAction g (ρ a) (hρ a) ≫ baseChangeAction g (ρ b) (hρ b) =
      baseChangeAction g (ρ (a * b)) (hρ (a * b)) := by
  rw [baseChangeAction_comp]
  congr 1
  exact hmul a b

/-- The *trace* `g_* j_g^* H ⟶ H` of a Galois covering, for the pullback computed by
restriction along the localization functor: the factorization of the norm `∑ a, ρ a` through
the unit. -/
noncomputable def galoisTraceRestriction (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (g)_*[AddCommGrpCat.{u + 1}].obj
      ((localizationRestriction AddCommGrpCat.{u + 1} g inferInstance).obj H) ⟶ H :=
  ObjectProperty.homMk (Presheaf.baseChangeTrace (ProEt.topology X)
    (fun a ↦ baseChangeAction g (ρ a) (hρ a)) (baseChangeAction_comp_mul g hρ hmul)
    (generate_singleton_baseChangeProj_mem g) (isGalois_baseChangeAction g hρ hgal)
    (isSheaf_comp_forget H))

/-- The action of `a : Γ` on `g_* j_g^* H`. -/
noncomputable def galoisActionRestriction (a : Γ)
    (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (g)_*[AddCommGrpCat.{u + 1}].obj
      ((localizationRestriction AddCommGrpCat.{u + 1} g inferInstance).obj H) ⟶
    (g)_*[AddCommGrpCat.{u + 1}].obj
      ((localizationRestriction AddCommGrpCat.{u + 1} g inferInstance).obj H) :=
  ObjectProperty.homMk (Presheaf.baseChangeAction (baseChangeAction g (ρ a) (hρ a)) H.obj)

omit [Surjective g] [QuasiCompact g] in
lemma localizationRestrictionLowerStarAdjunction_unit_app_hom
    (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g
      inferInstance).unit.app H).hom = Presheaf.baseChangeUnit (baseChangeProj g) H.obj := by
  rfl

/-- The unit followed by the trace is multiplication by the order of `Γ`. -/
lemma unit_comp_galoisTraceRestriction (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g
      inferInstance).unit.app H ≫
      galoisTraceRestriction g hρ hmul hgal H = Fintype.card Γ • 𝟙 H := by
  apply (sheafToPresheaf _ _).map_injective
  rw [Functor.map_comp, Functor.map_nsmul]
  erw [CategoryTheory.Functor.map_id]
  exact Presheaf.baseChangeUnit_comp_baseChangeTrace (ProEt.topology X)
    (fun a ↦ baseChangeAction g (ρ a) (hρ a)) (baseChangeAction_comp_mul g hρ hmul)
    (generate_singleton_baseChangeProj_mem g) (isGalois_baseChangeAction g hρ hgal)
    (isSheaf_comp_forget H)
    fun a ↦ baseChangeAction_comp_proj g (ρ a) (hρ a)

/-- The trace followed by the unit is the norm `∑ a, ρ a`. -/
@[reassoc]
lemma galoisTraceRestriction_comp_unit (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    galoisTraceRestriction g hρ hmul hgal H ≫
      (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g
        inferInstance).unit.app H =
      ∑ a, galoisActionRestriction g hρ a H := by
  apply (sheafToPresheaf _ _).map_injective
  rw [Functor.map_comp, Functor.map_sum]
  exact Presheaf.baseChangeTrace_comp_baseChangeUnit (ProEt.topology X)
    (fun a ↦ baseChangeAction g (ρ a) (hρ a)) (baseChangeAction_comp_mul g hρ hmul)
    (generate_singleton_baseChangeProj_mem g) (isGalois_baseChangeAction g hρ hgal)
    (isSheaf_comp_forget H)

/-- The trace is natural. -/
lemma galoisTraceRestriction_naturality {H H' : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}}
    (φ : H ⟶ H') :
    (g)_*[AddCommGrpCat.{u + 1}].map
        ((localizationRestriction AddCommGrpCat.{u + 1} g inferInstance).map φ) ≫
      galoisTraceRestriction g hρ hmul hgal H' = galoisTraceRestriction g hρ hmul hgal H ≫ φ := by
  apply (sheafToPresheaf _ _).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  exact Presheaf.baseChangeTrace_naturality (ProEt.topology X)
    (fun a ↦ baseChangeAction g (ρ a) (hρ a)) (baseChangeAction_comp_mul g hρ hmul)
    (generate_singleton_baseChangeProj_mem g) (isGalois_baseChangeAction g hρ hgal)
    (isSheaf_comp_forget H) (isSheaf_comp_forget H') φ.hom

/-- The comparison `g^* ≅ j_g^*` of the pullback with restriction along the localization
functor. -/
noncomputable abbrev upperStarIsoRestriction :=
  upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g inferInstance

/-- **The trace of a Galois covering** `t : g_* g^* H ⟶ H` of pro-étale abelian sheaves. -/
noncomputable def galoisTrace (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (g)_*[AddCommGrpCat.{u + 1}].obj ((g)^*[AddCommGrpCat.{u + 1}].obj H) ⟶ H :=
  (g)_*[AddCommGrpCat.{u + 1}].map ((upperStarIsoRestriction g).hom.app H) ≫
    galoisTraceRestriction g hρ hmul hgal H

/-- The action of `a : Γ` on `g_* g^* H`. -/
noncomputable def galoisAction (a : Γ) (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (g)_*[AddCommGrpCat.{u + 1}].obj ((g)^*[AddCommGrpCat.{u + 1}].obj H) ⟶
      (g)_*[AddCommGrpCat.{u + 1}].obj ((g)^*[AddCommGrpCat.{u + 1}].obj H) :=
  (g)_*[AddCommGrpCat.{u + 1}].map ((upperStarIsoRestriction g).hom.app H) ≫
    galoisActionRestriction g hρ a H ≫
      (g)_*[AddCommGrpCat.{u + 1}].map ((upperStarIsoRestriction g).inv.app H)

omit [Surjective g] [QuasiCompact g] in
@[reassoc]
lemma upperStarLowerStarAdjunction_unit_app_comp
    (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H ≫
      (g)_*[AddCommGrpCat.{u + 1}].map ((upperStarIsoRestriction g).hom.app H) =
      (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g
        inferInstance).unit.app H :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ H

/-- **The unit followed by the trace is the degree**: `u ≫ t = |Γ| • 𝟙` for the unit
`u : H ⟶ g_* g^* H` of a Galois covering with group `Γ`. -/
theorem unit_comp_galoisTrace (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H ≫
      galoisTrace g hρ hmul hgal H = Fintype.card Γ • 𝟙 H := by
  rw [galoisTrace]
  erw [upperStarLowerStarAdjunction_unit_app_comp_assoc]
  exact unit_comp_galoisTraceRestriction g hρ hmul hgal H

/-- **The trace followed by the unit is the norm**: `t ≫ u = ∑ a, ρ a`. -/
theorem galoisTrace_comp_unit (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    galoisTrace g hρ hmul hgal H ≫
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H =
      ∑ a, galoisAction g hρ a H := by
  have h : (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H =
      (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g
        inferInstance).unit.app H ≫
        (g)_*[AddCommGrpCat.{u + 1}].map ((upperStarIsoRestriction g).inv.app H) := by
    erw [← upperStarLowerStarAdjunction_unit_app_comp_assoc g H]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, comp_id]
  rw [galoisTrace, h, assoc, galoisTraceRestriction_comp_unit_assoc, Preadditive.sum_comp,
    Preadditive.comp_sum]
  rfl

/-- The trace of a Galois covering is natural. -/
theorem galoisTrace_naturality {H H' : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}}
    (φ : H ⟶ H') :
    (g)_*[AddCommGrpCat.{u + 1}].map ((g)^*[AddCommGrpCat.{u + 1}].map φ) ≫
      galoisTrace g hρ hmul hgal H' = galoisTrace g hρ hmul hgal H ≫ φ := by
  rw [galoisTrace, galoisTrace, ← Functor.map_comp_assoc]
  erw [(upperStarIsoRestriction g).hom.naturality φ]
  rw [Functor.map_comp_assoc, galoisTraceRestriction_naturality, assoc]

end Trace

end AlgebraicGeometry.ProEtale
