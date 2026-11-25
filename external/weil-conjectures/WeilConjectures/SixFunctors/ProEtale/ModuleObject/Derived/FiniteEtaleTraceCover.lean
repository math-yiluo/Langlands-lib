/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTraceModule

/-!
# Finite étale morphisms are pro-étale locally split

Let `g : Y ⟶ X` be finite étale. Every weakly étale `X`-scheme `V` is covered by étale
`V`-schemes `T` over which `T ×_X Y` splits as a finite disjoint union of copies of `T`
(`AlgebraicGeometry.finite_etale_etale_local_split`); such a cover is a pro-étale cover.
Hence (`AlgebraicGeometry.ProEtale.isLocallySplit_of_finite_of_etale`) `g` is pro-étale
locally split into `d` sheets as soon as every splitting over a nonempty base has `d` sheets,
that is, as soon as `g` has constant degree `d`.

Consequently, for `ℚ̲̄_ℓ`-coefficients, the unit of `Lg^* ⊣ Rg_*` is a split monomorphism for a
finite étale `g` of constant degree `d ≠ 0`
(`isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_finite_of_etale`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g] [Etale g]

/-- Every point `v` of a weakly étale `X`-scheme `V` lies in the image of an étale
`V`-scheme `T`, produced by
`AlgebraicGeometry.finite_etale_etale_local_split`, over which `T ×_X Y` splits. -/
lemma exists_traceSplitting_of_etale_local_split (V : X.ProEt) (v : V.left) :
    ∃ (T : X.ProEt) (k : T ⟶ V) (_ : TraceSplitting g T),
      Nonempty T.left ∧ v ∈ Set.range k.left ∧ Etale k.left := by
  classical
  obtain ⟨U, e, z, he, hz, J, W, i, hJ, hc, -, hd⟩ :=
    finite_etale_etale_local_split (pullback.fst V.hom g) v
  have : Etale e := he
  have : Fintype J := Fintype.ofFinite J
  have : WeaklyEtale (e ≫ V.hom) := inferInstance
  let T : X.ProEt := ProEt.mk (e ≫ V.hom)
  let k : T ⟶ V := MorphismProperty.Over.homMk e rfl
  let iso : pullback (pullback.fst V.hom g) e ≅ pullback T.hom g :=
    pullbackSymmetry (pullback.fst V.hom g) e ≪≫ pullbackRightPullbackFstIso V.hom g e
  choose dj hdj using hd
  have hsl (j : J) : ((dj j).inv ≫ i j ≫ iso.hom) ≫ pullback.fst T.hom g = 𝟙 U := by
    have h₁ : iso.hom ≫ pullback.fst T.hom g = pullback.snd (pullback.fst V.hom g) e := by
      change _ ≫ _ ≫ pullback.fst (e ≫ V.hom) g = _
      simp
    rw [Category.assoc, Category.assoc, h₁, ← hdj, Iso.inv_hom_id]
  let s (j : J) : T ⟶ (traceBaseChange g).obj T :=
    MorphismProperty.Over.homMk ((dj j).inv ≫ i j ≫ iso.hom) (by
      change ((dj j).inv ≫ i j ≫ iso.hom) ≫ pullback.snd T.hom g ≫ g = T.hom
      rw [← pullback.condition, ← Category.assoc, hsl j, Category.id_comp])
  refine ⟨T, k, ⟨J, s, fun j ↦ MorphismProperty.Over.Hom.ext (hsl j), ?_⟩, ⟨z⟩, ⟨z, hz⟩, he⟩
  have hc₁ : IsColimit (Cofan.mk (pullback T.hom g) fun j ↦ i j ≫ iso.hom) :=
    IsColimit.ofIsoColimit hc.some (Cofan.ext iso (fun _ ↦ rfl))
  let α : Discrete.functor W ≅ Discrete.functor (fun _ : J ↦ U) :=
    Discrete.natIso fun j ↦ dj j.as
  refine (IsColimit.precomposeHomEquiv α _)
    (IsColimit.ofIsoColimit hc₁ (Cocone.ext (Iso.refl _) ?_))
  rintro ⟨j⟩
  change (i j ≫ iso.hom) ≫ 𝟙 _ = (dj j).hom ≫ (dj j).inv ≫ i j ≫ iso.hom
  rw [Category.comp_id, Iso.hom_inv_id_assoc]

/-- A **finite étale morphism is pro-étale locally split**: if every splitting of `g` over a
nonempty weakly étale `X`-scheme has `d` sheets (i.e. `g` has constant degree `d`), then `g` is
pro-étale locally split into `d` sheets. -/
theorem isLocallySplit_of_finite_of_etale {d : ℕ}
    (hsheets : ∀ (T : X.ProEt) (D : TraceSplitting g T), Nonempty T.left →
      Fintype.card D.J = d) :
    IsLocallySplit g d := by
  intro V
  choose T k D hne hv he using exists_traceSplitting_of_etale_local_split g V
  rw [ProEt.mem_topology_iff]
  refine ⟨.ofArrows T k, ?_, fun _ _ h ↦ ?_⟩
  · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact etalePrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun v ↦ ⟨v, hv v⟩, fun v ↦ he v⟩)
  · obtain ⟨v⟩ := h
    exact ⟨D v, hsheets _ _ (hne v)⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- **Split derived units along a finite étale cover**, for `ℚ̲̄_ℓ`-coefficients: let
`g : Y ⟶ X` be finite étale of constant degree `d ≠ 0`, in the sense that every splitting of `g`
over a nonempty weakly étale `X`-scheme has `d` sheets. Then the unit of the derived adjunction
`Lg^* ⊣ Rg_*` is a split monomorphism at every complex. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_finite_of_etale
    (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g] [Etale g] {d : ℕ}
    (hd : d ≠ 0)
    (hsheets : ∀ (T : X.ProEt) (D : TraceSplitting g T), Nonempty T.left →
      Fintype.card D.J = d)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      g).unit.app G) :=
  isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_isLocallySplit
    (isLocallySplit_of_finite_of_etale g hsheets) ℓ hd G

end AlgebraicGeometry.ProEtale.CondensedRing
