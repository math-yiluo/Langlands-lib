/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTraceSplitSum

/-!
# The trace of a locally split cover on pro-étale sheaves

Let `g : Y ⟶ X` be weakly étale, and assume that `g` is *pro-étale locally split into `d`
sheets*: every weakly étale `X`-scheme `V` is covered by `T ⟶ V` over which `T ×_X Y` is the
disjoint union of `d` copies of `T` (`AlgebraicGeometry.ProEtale.splitSieve`). This holds for a
finite étale `g` of constant degree `d`.

For a sheaf `G` on `X_proét` with values in a preadditive category, the traces along the local
splittings (`AlgebraicGeometry.ProEtale.TraceSplitting.trace`) glue to a trace
`G(V ×_X Y) ⟶ G(V)` (`AlgebraicGeometry.ProEtale.splitTraceApp`), which is natural in `V`
and in `G` and whose composite with the restriction along the projection `V ×_X Y ⟶ V` is
multiplication by `d` (`AlgebraicGeometry.ProEtale.restriction_comp_splitTraceApp`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g] (d : ℕ)

/-- The sieve of `T ⟶ V` such that `T ×_X Y` splits over `T` into `d` sheets. -/
def splitSieve (V : X.ProEt) : Sieve V where
  arrows T _ := ∃ D : TraceSplitting g T, Fintype.card D.J = d
  downward_closed := fun {_ _} _ ⟨D, hD⟩ k ↦ ⟨D.restrict k, hD⟩

/-- `g` is **pro-étale locally split into `d` sheets** if every weakly étale `X`-scheme is
covered by objects over which `g` splits into `d` sheets. -/
def IsLocallySplit : Prop := ∀ V : X.ProEt, splitSieve g d V ∈ ProEt.topology X V

variable {g d} (hg : IsLocallySplit g d) {A : Type u'} [Category.{u + 1} A] [Preadditive A]
  (G : Sheaf (ProEt.topology X) A)

/-- The **trace** `G(V ×_X Y) ⟶ G(V)` of a locally split cover: the amalgamation of the traces
along local splittings. -/
noncomputable def splitTraceApp (V : X.ProEt) :
    G.obj.obj (op ((traceBaseChange g).obj V)) ⟶ G.obj.obj (op V) :=
  G.property.amalgamate ⟨splitSieve g d V, hg V⟩
    (fun I ↦ G.obj.map ((traceBaseChange g).map I.f).op ≫ I.hf.choose.trace G)
    (by
      intro I₁ I₂ r
      simp only [Category.assoc]
      rw [← TraceSplitting.trace_restrict_naturality I₁.hf.choose r.g₁ G
          (I₁.hf.choose.restrict r.g₁),
        ← TraceSplitting.trace_restrict_naturality I₂.hf.choose r.g₂ G
          (I₁.hf.choose.restrict r.g₁),
        ← G.obj.map_comp_assoc, ← G.obj.map_comp_assoc, ← op_comp, ← op_comp,
        ← Functor.map_comp, ← Functor.map_comp, r.w])

include hg in
/-- The trace restricted along `k : T ⟶ V` is computed by any splitting of `T ×_X Y`. -/
lemma splitTraceApp_comp {T V : X.ProEt} (k : T ⟶ V) (D : TraceSplitting g T) :
    splitTraceApp hg G V ≫ G.obj.map k.op =
      G.obj.map ((traceBaseChange g).map k).op ≫ D.trace G := by
  refine G.property.hom_ext ⟨splitSieve g d T, hg T⟩ _ _ fun I ↦ ?_
  obtain ⟨D', hD'⟩ := I.hf
  rw [Category.assoc, ← G.obj.map_comp, ← op_comp, splitTraceApp,
    Presheaf.IsSheaf.amalgamate_map (I := ⟨_, I.f ≫ k,
      show ∃ D : TraceSplitting g I.Y, Fintype.card D.J = d from ⟨D', hD'⟩⟩),
    TraceSplitting.trace_eq G _ D', Category.assoc,
    ← TraceSplitting.trace_restrict_naturality D I.f G D', ← G.obj.map_comp_assoc, ← op_comp,
    ← Functor.map_comp]

include hg in
/-- The trace is natural in the weakly étale `X`-scheme `V`. -/
lemma splitTraceApp_naturality {V V' : X.ProEt} (f : V' ⟶ V) :
    G.obj.map ((traceBaseChange g).map f).op ≫ splitTraceApp hg G V' =
      splitTraceApp hg G V ≫ G.obj.map f.op := by
  refine G.property.hom_ext ⟨splitSieve g d V', hg V'⟩ _ _ fun I ↦ ?_
  obtain ⟨D, -⟩ := I.hf
  rw [Category.assoc, splitTraceApp_comp hg G I.f D, Category.assoc, ← G.obj.map_comp,
    ← op_comp,
    splitTraceApp_comp hg G (I.f ≫ f) D, ← G.obj.map_comp_assoc, ← op_comp, Functor.map_comp]

include hg in
/-- The restriction along the projection `V ×_X Y ⟶ V` followed by the trace is multiplication
by the number `d` of sheets. -/
lemma restriction_comp_splitTraceApp (V : X.ProEt) :
    G.obj.map (traceProj g V).op ≫ splitTraceApp hg G V = d • 𝟙 _ := by
  refine G.property.hom_ext ⟨splitSieve g d V, hg V⟩ _ _ fun I ↦ ?_
  obtain ⟨D, hD⟩ := I.hf
  rw [Category.assoc, splitTraceApp_comp hg G I.f D, ← G.obj.map_comp_assoc, ← op_comp,
    traceBaseChange_map_comp_traceProj, op_comp, G.obj.map_comp_assoc,
    TraceSplitting.restriction_comp_trace, hD, Preadditive.comp_nsmul, Preadditive.nsmul_comp,
    Category.comp_id, Category.id_comp]

/-- The trace along a splitting is natural in the sheaf. -/
lemma TraceSplitting.trace_naturality_sheaf {G G' : Sheaf (ProEt.topology X) A} (ψ : G ⟶ G')
    {T : X.ProEt} (D : TraceSplitting g T) :
    D.trace G ≫ ψ.hom.app (op T) =
      ψ.hom.app (op ((traceBaseChange g).obj T)) ≫ D.trace G' := by
  simp only [TraceSplitting.trace, Preadditive.sum_comp, Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun j _ ↦ ψ.hom.naturality (D.s j).op

include hg in
/-- The trace is natural in the sheaf `G`. -/
lemma splitTraceApp_naturality_sheaf {G G' : Sheaf (ProEt.topology X) A} (ψ : G ⟶ G')
    (V : X.ProEt) :
    splitTraceApp hg G V ≫ ψ.hom.app (op V) =
      ψ.hom.app (op ((traceBaseChange g).obj V)) ≫ splitTraceApp hg G' V := by
  refine G'.property.hom_ext ⟨splitSieve g d V, hg V⟩ _ _ fun I ↦ ?_
  obtain ⟨D, -⟩ := I.hf
  rw [Category.assoc, ← ψ.hom.naturality, reassoc_of% (splitTraceApp_comp hg G I.f D),
    D.trace_naturality_sheaf, Category.assoc, splitTraceApp_comp hg G' I.f D,
    ← ψ.hom.naturality_assoc]
  rfl

section Sheaf

variable (A' : Type u') [Category.{u + 1} A'] [Abelian A']

/-- The **trace** `g_* g^* G ⟶ G` of a pro-étale locally split cover, on sheaves (with `g^*`
computed by restriction along the localization functor). -/
noncomputable def splitTrace :
    localizationRestriction A' g inferInstance ⋙ (g)_*[A'] ⟶ 𝟭 _ where
  app G := ObjectProperty.homMk
    { app := fun V ↦ splitTraceApp hg G V.unop
      naturality := fun _ _ f ↦ splitTraceApp_naturality hg G f.unop }
  naturality _ _ ψ := Sheaf.hom_ext (NatTrans.ext (funext fun V ↦
    (splitTraceApp_naturality_sheaf hg ψ V.unop).symm))

lemma splitTrace_app_hom_app (G : Sheaf (ProEt.topology X) A') (V : X.ProEt) :
    ((splitTrace hg A').app G).hom.app (op V) = splitTraceApp hg G V := rfl

omit [Abelian A'] in
/-- The unit of `g^* ⊣ g_*` restricts sections along the projection `V ×_X Y ⟶ V`. -/
lemma localizationRestrictionLowerStarAdjunction_unit_app_hom_app_traceProj
    (G : Sheaf (ProEt.topology X) A') (V : X.ProEt) :
    ((localizationRestrictionLowerStarAdjunction A' g inferInstance).unit.app G).hom.app (op V) =
      G.obj.map (traceProj g V).op := by
  simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
    Adjunction.whiskerLeft]

/-- The unit of `g^* ⊣ g_*` followed by the trace of a cover locally split into `d` sheets is
multiplication by `d`. -/
lemma unit_comp_splitTrace :
    (localizationRestrictionLowerStarAdjunction A' g inferInstance).unit ≫ splitTrace hg A' =
      d • 𝟙 _ := by
  refine NatTrans.ext (funext fun G ↦ Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ?_)))
  induction V using Opposite.rec with | op V => ?_
  have h : (d • 𝟙 G).hom = d • 𝟙 G.obj :=
    (sheafToPresheaf (ProEt.topology X) A').map_nsmul (f := 𝟙 G) (n := d)
  simp only [NatTrans.comp_app, NatTrans.app_nsmul, NatTrans.id_app, Functor.id_obj]
  rw [h, NatTrans.app_nsmul, NatTrans.id_app, ← restriction_comp_splitTraceApp hg G V,
    ← localizationRestrictionLowerStarAdjunction_unit_app_hom_app_traceProj]
  rfl
end Sheaf

end AlgebraicGeometry.ProEtale
