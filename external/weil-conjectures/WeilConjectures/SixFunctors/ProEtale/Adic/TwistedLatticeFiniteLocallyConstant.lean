/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedFiniteEtale
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedModule
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale
public import WeilConjectures.ConstructibleSheaf.OfForget
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SetLocallyConstant

/-!
# Twisted sheaves with finite fibres are finite locally constant

Let `f : V ⟶ Y` be weakly étale, surjective and quasi-compact, `Y` quasi-separated, and `c` a
descent cocycle on the constant sheaf `S_V` of a finite set `S`. The étale sheaf of sets of
twisted sections of `c` is represented by a finite étale `Y`-scheme (descent of finite étale
morphisms, `AlgebraicGeometry.TwistedDescent.exists_isUniversalSection`, glued along a Zariski
cover), hence is finite locally constant
(`AlgebraicGeometry.isFiniteLocallyConstantSheafOfTypes_twistedSectionsPresheaf`). For a linear
cocycle on a finite module over a finite ring, the étale sheaf of modules of twisted sections is
finite locally constant (`AlgebraicGeometry.isFiniteLocallyConstantSheaf_twistedModuleSheaf`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {Y V : Scheme.{u}} (f : V ⟶ Y)


variable [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparatedSpace Y]

/-- **The twisted sections of a descent cocycle on `Fin N` are represented by a finite étale
`Y`-scheme.** -/
theorem exists_isUniversalSection_twistedSectionsPresheaf {N : ℕ}
    {c : ↥(pullback f f) → Fin N → Fin N} (hc : IsDescentCocycle f c) :
    ∃ (P : Scheme.{u}) (π : P ⟶ Y) (_ : AlgebraicGeometry.Etale π) (_ : IsFinite π)
      (ξ : (twistedSectionsPresheaf f c).obj (op (Scheme.Etale.mk (π ≫ 𝟙 Y)))),
      IsUniversalSection (twistedSectionsPresheaf f c) (𝟙 Y) (Scheme.Etale.mk (π ≫ 𝟙 Y)) π ξ := by
  have H (y : Y) : ∃ O : Y.Opens, y ∈ O ∧
      IsRepresentableOver (twistedSectionsPresheaf f c) (𝟙 Y) O := by
    obtain ⟨O, hO, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
    have : IsAffine O := hO
    obtain ⟨W, _, j, p, _, _, hjp⟩ := exists_affine_weaklyEtale_cover f (O.ι ≫ 𝟙 Y)
    have : WeaklyEtale (j ≫ f) := hjp ▸ inferInstance
    have : QuasiCompact (j ≫ f) := hjp ▸ inferInstance
    obtain ⟨Nsch, n, hn, hnf, ξ, hξ, -⟩ :=
      TwistedDescent.exists_isUniversalSection hc (O.ι ≫ 𝟙 Y) j p hjp
    exact ⟨O, hy, Nsch, n, hn, hnf, ξ, hξ⟩
  exact Scheme.exists_isUniversalSection_of_forall_exists_opens
    (isSheaf_twistedSectionsPresheaf f c) (𝟙 Y) H


omit [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparatedSpace Y] in
/-- Transporting a descent cocycle along a bijection. -/
lemma IsDescentCocycle.transport {S S' : Type*} {c : ↥(pullback f f) → S → S}
    (hc : IsDescentCocycle f c) (e : S ≃ S') :
    IsDescentCocycle f (fun z ↦ e ∘ c z ∘ e.symm) where
  isLocallyConstant s := (hc.isLocallyConstant (e.symm s)).comp e
  bijective z := e.bijective.comp ((hc.bijective z).comp e.symm.bijective)
  diagonal v := by
    funext s
    simp [hc.diagonal]
  cocycle w := by
    funext s
    simp [hc.cocycle]

/-- **The twisted sections of a descent cocycle on a finite set are represented by a finite étale
`Y`-scheme.** -/
theorem exists_iso_uliftYoneda_twistedSectionsPresheaf {S : Type (u + 1)} [Finite S]
    {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c) :
    ∃ (P : Scheme.{u}) (π : P ⟶ Y) (_ : AlgebraicGeometry.Etale π) (_ : IsFinite π),
      Nonempty (twistedSectionsPresheaf f c ≅ uliftYoneda.{u + 1}.obj (Scheme.Etale.mk π)) := by
  obtain ⟨K, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  obtain ⟨P, π, _, _, ξ, hξ⟩ := exists_isUniversalSection_twistedSectionsPresheaf f
    (hc.transport f e)
  have hξ' := (hξ.of_eq (Category.comp_id π).symm).bijective_of_id
  let E' := twistedSectionsPresheaf f (fun z ↦ e ∘ c z ∘ e.symm)
  -- the transport of twisted sections along `e`
  let t (W : Y.Etale) : E'.obj (op W) → (twistedSectionsPresheaf f c).obj (op W) :=
    fun σ ↦ ⟨e.symm ∘ σ.1, σ.2.1.comp _, fun w ↦ by
      have := σ.2.2 w
      simp only [Function.comp_apply] at this ⊢
      rw [this, Equiv.symm_apply_apply]⟩
  have ht (W : Y.Etale) : Function.Bijective (t W) := by
    refine ⟨fun σ τ h ↦ Subtype.ext (funext fun x ↦ e.symm.injective ?_), fun σ ↦ ?_⟩
    · exact congrFun (congrArg Subtype.val h) x
    · refine ⟨⟨e ∘ σ.1, σ.2.1.comp _, fun w ↦ ?_⟩, Subtype.ext (funext fun x ↦ ?_)⟩
      · have := σ.2.2 w
        simp only [Function.comp_apply] at this ⊢
        rw [this, Equiv.symm_apply_apply]
      · simp [t]
  refine ⟨P, π, inferInstance, inferInstance, ⟨?_⟩⟩
  refine (NatIso.ofComponents (fun W ↦ (Equiv.ofBijective
      (fun a : ULift.{u + 1} (W.unop ⟶ Scheme.Etale.mk (π ≫ 𝟙 Y)) ↦ t W.unop (E'.map a.down.op ξ))
      ((ht W.unop).comp ((hξ' W.unop).comp Equiv.ulift.bijective))).toIso)
      (fun {W W'} g ↦ ?_)).symm ≪≫
    uliftYoneda.{u + 1}.mapIso (MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 P ≫ π = π ≫ 𝟙 Y
      rw [Category.id_comp, Category.comp_id]))
  ext a
  refine Subtype.ext ?_
  change e.symm ∘ (E'.map (g.unop ≫ a.down).op ξ).1 = (e.symm ∘ (E'.map a.down.op ξ).1) ∘ _
  rw [op_comp, Functor.map_comp_apply]
  rfl

/-- **Twisted sheaves of sets with finite fibres are finite locally constant.** -/
theorem isFiniteLocallyConstantSheafOfTypes_twistedSectionsPresheaf {S : Type (u + 1)}
    [Finite S] {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c) :
    IsFiniteLocallyConstantSheafOfTypes
      (⟨twistedSectionsPresheaf f c, isSheaf_twistedSectionsPresheaf f c⟩ :
        Sheaf Y.smallEtaleTopology (Type (u + 1))) := by
  obtain ⟨P, π, _, _, ⟨e⟩⟩ := exists_iso_uliftYoneda_twistedSectionsPresheaf f hc
  obtain ⟨hsh, hcov, hfin⟩ := isFiniteLocallyConstant_uliftYoneda P π
  exact IsFiniteLocallyConstantSheafOfTypes.of_iso
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso
      (X := ⟨uliftYoneda.obj (Scheme.Etale.mk π), hsh⟩)
      (Y := ⟨twistedSectionsPresheaf f c, isSheaf_twistedSectionsPresheaf f c⟩) e.symm)
    ⟨hcov, hfin⟩

/-- **Twisted sheaves of modules with finite fibres are finite locally constant**: for a linear
descent cocycle on a finite module over a finite ring, the étale sheaf of twisted sections is
finite locally constant. -/
theorem isFiniteLocallyConstantSheaf_twistedModuleSheaf {Λ : Type (u + 1)} [CommRing Λ]
    [Finite Λ] {M : Type (u + 1)} [AddCommGroup M] [Module Λ M] [Finite M]
    (c : ↥(pullback f f) → M ≃ₗ[Λ] M) (hc : IsDescentCocycle f (fun z ↦ c z)) :
    IsFiniteLocallyConstantSheaf (twistedModuleSheaf f c) :=
  IsFiniteLocallyConstantSheaf.of_forget _ (IsFiniteLocallyConstantSheafOfTypes.of_iso
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso
      (X := ⟨twistedSectionsPresheaf f (fun z ↦ c z), isSheaf_twistedSectionsPresheaf f _⟩)
      (Y := (sheafCompose _ (forget (ModuleCat.{u + 1} Λ))).obj (twistedModuleSheaf f c))
      (twistedModulePresheafCompForgetIso f c).symm)
    (isFiniteLocallyConstantSheafOfTypes_twistedSectionsPresheaf f hc))

end AlgebraicGeometry
