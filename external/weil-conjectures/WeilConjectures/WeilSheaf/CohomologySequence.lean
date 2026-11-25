/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.HomologySequence
public import WeilConjectures.WeilSheaf.StalkFunctor

/-!
# The long exact sequence of compactly supported cohomology

The global sections `Γ(X̄, -)` of Weil sheaves are left exact, and on `Spec k₀`, whose geometric
fiber is the spectrum of the algebraically closed field `k̄`, they are exact. Together with the
long exact sequence of cohomology sheaves (`WeilConjectures.WeilSheaf.HomologySequence`) and the
triangulated direct image with compact support `Ra_!`, this gives, for a distinguished triangle
`K₁ → K₂ → K₃ → K₁[1]` of Weil complexes on a separated `k₀`-scheme of finite type, the long exact
sequence of Frobenius-equivariant maps

`⋯ → H_c^n(K₁) → H_c^n(K₂) → H_c^n(K₃) → H_c^{n+1}(K₁) → ⋯`.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.globalSectionsLinearMap`: the Frobenius-equivariant linear map of
  global sections induced by a morphism of Weil sheaves.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomologyMap`: the map `H_c^n(K) → H_c^n(L)`
  induced by a morphism of Weil complexes.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomologyδ`: the connecting map of a
  triangle.

## Main results

- `AlgebraicGeometry.WeilComplex.exact_compactlySupportedCohomologyMap`,
  `exact_compactlySupportedCohomologyδ_left`, `exact_compactlySupportedCohomologyδ_right`:
  exactness of the long exact sequence.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

section GlobalSections

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The `ℚ̄_ℓ`-linear map of global sections induced by a morphism of Weil sheaves. -/
noncomputable def globalSectionsLinearMap {G G' : WeilSheaf k₀ l X} (f : G ⟶ G') :
    G.globalSections.carrier →ₗ[PadicAlgCl l] G'.globalSections.carrier :=
  ((WeilCoefficients.toModuleCat l).map (globalSectionsMap f)).hom

/-- The map of global sections commutes with the Frobenius. -/
lemma globalSectionsLinearMap_frobenius {G G' : WeilSheaf k₀ l X} (f : G ⟶ G')
    (x : G.globalSections.carrier) :
    globalSectionsLinearMap f (G.globalSections.frobenius x) =
      G'.globalSections.frobenius (globalSectionsLinearMap f x) := by
  have h := congrArg (fun g ↦ ((WeilCoefficients.toModuleCat l).map g).hom x)
    (globalSectionsMap_comp_frobeniusHom f)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

variable (k₀ l X) in
/-- The global sections functor `F ↦ Γ(X̄, F)` on Weil sheaves. -/
noncomputable abbrev globalSectionsFunctor : WeilSheaf k₀ l X ⥤ WeilCoefficients.{u} l :=
  sheafFunctor k₀ l X ⋙ Sheaf.Γ _ _

instance : PreservesFiniteLimits (globalSectionsFunctor k₀ l X) := by
  infer_instance

/-- The global sections on `Spec k₀` preserve epimorphisms: the geometric fiber of `Spec k₀` is
the spectrum of the algebraically closed field `k̄`, every pro-étale covering of which splits. -/
instance : (globalSectionsFunctor k₀ l (Spec (CommRingCat.of k₀))).PreservesEpimorphisms where
  preserves {F G} φ _ := by
    have e : (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
        Spec (.of (AlgebraicClosure k₀)) :=
      have : IsIso (Spec (CommRingCat.of k₀) ↘
          Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure := by
        unfold Scheme.Hom.geometricFiberToAlgebraicClosure
        infer_instance
      asIso (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    let e' := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId _)
    have hepi : Epi ((sheafFunctor k₀ l (Spec (CommRingCat.of k₀))).map φ) := inferInstance
    have h : (globalSectionsFunctor k₀ l _).map φ =
        e'.hom.app _ ≫ ((sheafSections _ _).obj _).map ((sheafFunctor k₀ l _).map φ) ≫
          e'.inv.app _ := by
      rw [← reassoc_of% (e'.hom.naturality _)]
      simp
    have : Epi (((sheafSections _ (WeilCoefficients.{u} l)).obj (Opposite.op
        (Scheme.ProEt.mk (𝟙 _)))).map ((sheafFunctor k₀ l _).map φ)) :=
      (ModuleCat.epi_iff_surjective _).2 (ProEtale.surjective_app_of_epi_of_iso e _)
    rw [h]
    infer_instance

/-- The global sections on `Spec k₀` are exact. -/
instance : (globalSectionsFunctor k₀ l (Spec (CommRingCat.of k₀))).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- An exact sequence of Weil sheaves on `Spec k₀` gives an exact sequence of global sections. -/
lemma exact_globalSectionsLinearMap
    {S : ShortComplex (WeilSheaf k₀ l (Spec (CommRingCat.of k₀)))} (hS : S.Exact) :
    Function.Exact (globalSectionsLinearMap S.f) (globalSectionsLinearMap S.g) := by
  have h :=
    (hS.map (globalSectionsFunctor k₀ l (Spec (CommRingCat.of k₀)))).moduleCat_range_eq_ker
  intro y
  constructor
  · intro hy
    have hy' : y ∈ LinearMap.ker (S.map (globalSectionsFunctor k₀ l _)).g.hom := hy
    rw [← h] at hy'
    obtain ⟨x, hx⟩ := hy'
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    have hx : (S.map (globalSectionsFunctor k₀ l _)).f.hom x ∈
        LinearMap.range (S.map (globalSectionsFunctor k₀ l _)).f.hom := ⟨x, rfl⟩
    rw [h] at hx
    exact hx

end GlobalSections

end WeilSheaf

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The map `H_c^r(K) → H_c^r(L)` induced by a morphism `f : K ⟶ L` of Weil complexes. -/
noncomputable def compactlySupportedCohomologyMap {K L : WeilComplex k₀ l X} (f : K ⟶ L)
    (r : ℤ) :
    (K.compactlySupportedCohomology r).carrier →ₗ[PadicAlgCl l]
      (L.compactlySupportedCohomology r).carrier :=
  WeilSheaf.globalSectionsLinearMap
    ((homologySheaf r).map ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map f))

/-- The map induced on compactly supported cohomology commutes with the Frobenius. -/
lemma compactlySupportedCohomologyMap_frobenius {K L : WeilComplex k₀ l X} (f : K ⟶ L) (r : ℤ)
    (x : (K.compactlySupportedCohomology r).carrier) :
    compactlySupportedCohomologyMap f r ((K.compactlySupportedCohomology r).frobenius x) =
      (L.compactlySupportedCohomology r).frobenius (compactlySupportedCohomologyMap f r x) :=
  WeilSheaf.globalSectionsLinearMap_frobenius _ x

variable (T : Triangle (WeilComplex k₀ l X)) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

/-- The image `Ra_!K₁ → Ra_!K₂ → Ra_!K₃ → Ra_!K₁[1]` of a triangle of Weil complexes under the
direct image with compact support to `Spec k₀`. -/
noncomputable abbrev derivedLowerShriekTriangle :
    Triangle (WeilComplex k₀ l (Spec (CommRingCat.of k₀))) :=
  Triangle.mk ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map T.mor₁)
    ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map T.mor₂)
    ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map T.mor₃ ≫
      ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).commShiftIso 1).hom.app T.obj₁)

/-- The connecting map `H_c^{n₀}(K₃) → H_c^{n₁}(K₁)`, `n₁ = n₀ + 1`, of a triangle
`K₁ → K₂ → K₃ → K₁[1]` of Weil complexes. -/
noncomputable def compactlySupportedCohomologyδ :
    (T.obj₃.compactlySupportedCohomology n₀).carrier →ₗ[PadicAlgCl l]
      (T.obj₁.compactlySupportedCohomology n₁).carrier :=
  WeilSheaf.globalSectionsLinearMap (homologySheafδ (derivedLowerShriekTriangle T) n₀ n₁ h)

/-- The connecting map commutes with the Frobenius. -/
lemma compactlySupportedCohomologyδ_frobenius
    (x : (T.obj₃.compactlySupportedCohomology n₀).carrier) :
    compactlySupportedCohomologyδ T n₀ n₁ h
        ((T.obj₃.compactlySupportedCohomology n₀).frobenius x) =
      (T.obj₁.compactlySupportedCohomology n₁).frobenius
        (compactlySupportedCohomologyδ T n₀ n₁ h x) :=
  WeilSheaf.globalSectionsLinearMap_frobenius _ x

variable (hT : T ∈ distTriang (WeilComplex k₀ l X))
include hT

/-- The image of a distinguished triangle under `Ra_!` is distinguished. -/
lemma derivedLowerShriekTriangle_distinguished :
    derivedLowerShriekTriangle T ∈ distTriang (WeilComplex k₀ l (Spec (CommRingCat.of k₀))) := by
  have := (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map_distinguished T hT
  rwa [Functor.mapTriangle_obj] at this

/-- Exactness of `H_c^n(K₁) → H_c^n(K₂) → H_c^n(K₃)`. -/
lemma exact_compactlySupportedCohomologyMap :
    Function.Exact (compactlySupportedCohomologyMap T.mor₁ n₀)
      (compactlySupportedCohomologyMap T.mor₂ n₀) := by
  -- Infer the short complex before comparing the global sections with the goal.
  have hExact := WeilSheaf.exact_globalSectionsLinearMap
    (homologySheaf_exact₂ _ n₀ (derivedLowerShriekTriangle_distinguished T hT))
  exact hExact

/-- Exactness of `H_c^{n₀}(K₂) → H_c^{n₀}(K₃) → H_c^{n₁}(K₁)`. -/
lemma exact_compactlySupportedCohomologyδ_left :
    Function.Exact (compactlySupportedCohomologyMap T.mor₂ n₀)
      (compactlySupportedCohomologyδ T n₀ n₁ h) := by
  have hExact := WeilSheaf.exact_globalSectionsLinearMap
    (homologySheaf_exact₃ _ n₀ n₁ (derivedLowerShriekTriangle_distinguished T hT) h)
  exact hExact

/-- Exactness of `H_c^{n₀}(K₃) → H_c^{n₁}(K₁) → H_c^{n₁}(K₂)`. -/
lemma exact_compactlySupportedCohomologyδ_right :
    Function.Exact (compactlySupportedCohomologyδ T n₀ n₁ h)
      (compactlySupportedCohomologyMap T.mor₁ n₁) := by
  have hExact := WeilSheaf.exact_globalSectionsLinearMap
    (homologySheaf_exact₁ _ n₀ n₁ (derivedLowerShriekTriangle_distinguished T hT) h)
  exact hExact

end WeilComplex

namespace WeilComplex

section SpecCohomology

variable {K L : WeilComplex k₀ l (Spec (CommRingCat.of k₀))}

/-- The map `Hʳ(Spec k̄, K) → Hʳ(Spec k̄, L)` induced by a morphism of Weil complexes on `Spec k₀`.
-/
noncomputable def cohomologyMap (f : K ⟶ L) (r : ℤ) :
    (K.cohomologyFrobeniusModule r).carrier →ₗ[PadicAlgCl l]
      (L.cohomologyFrobeniusModule r).carrier :=
  WeilSheaf.globalSectionsLinearMap ((homologySheaf r).map f)

lemma cohomologyMap_frobenius (f : K ⟶ L) (r : ℤ) (x : (K.cohomologyFrobeniusModule r).carrier) :
    cohomologyMap f r ((K.cohomologyFrobeniusModule r).frobenius x) =
      (L.cohomologyFrobeniusModule r).frobenius (cohomologyMap f r x) :=
  WeilSheaf.globalSectionsLinearMap_frobenius _ x

/-- An isomorphism of Weil complexes on `Spec k₀` induces isomorphisms of cohomology. -/
noncomputable def cohomologyEquivOfIso (e : K ≅ L) (r : ℤ) :
    (K.cohomologyFrobeniusModule r).Equiv (L.cohomologyFrobeniusModule r) :=
  WeilSheaf.globalSectionsEquivOfIso ((homologySheaf r).mapIso e)

variable (T : Triangle (WeilComplex k₀ l (Spec (CommRingCat.of k₀)))) (n₀ n₁ : ℤ)
  (h : n₀ + 1 = n₁)

/-- The connecting map `H^{n₀}(K₃) → H^{n₁}(K₁)` of a triangle of Weil complexes on `Spec k₀`. -/
noncomputable def cohomologyδ :
    (T.obj₃.cohomologyFrobeniusModule n₀).carrier →ₗ[PadicAlgCl l]
      (T.obj₁.cohomologyFrobeniusModule n₁).carrier :=
  WeilSheaf.globalSectionsLinearMap (homologySheafδ T n₀ n₁ h)

lemma cohomologyδ_frobenius (x : (T.obj₃.cohomologyFrobeniusModule n₀).carrier) :
    cohomologyδ T n₀ n₁ h ((T.obj₃.cohomologyFrobeniusModule n₀).frobenius x) =
      (T.obj₁.cohomologyFrobeniusModule n₁).frobenius (cohomologyδ T n₀ n₁ h x) :=
  WeilSheaf.globalSectionsLinearMap_frobenius _ x

variable (hT : T ∈ distTriang (WeilComplex k₀ l (Spec (CommRingCat.of k₀))))
include hT

lemma exact_cohomologyMap :
    Function.Exact (cohomologyMap T.mor₁ n₀) (cohomologyMap T.mor₂ n₀) := by
  -- Infer the short complex before comparing the global sections with the goal.
  have hExact := WeilSheaf.exact_globalSectionsLinearMap (homologySheaf_exact₂ T n₀ hT)
  exact hExact

lemma exact_cohomologyδ_left :
    Function.Exact (cohomologyMap T.mor₂ n₀) (cohomologyδ T n₀ n₁ h) := by
  have hExact := WeilSheaf.exact_globalSectionsLinearMap (homologySheaf_exact₃ T n₀ n₁ hT h)
  exact hExact

lemma exact_cohomologyδ_right :
    Function.Exact (cohomologyδ T n₀ n₁ h) (cohomologyMap T.mor₁ n₁) := by
  have hExact := WeilSheaf.exact_globalSectionsLinearMap (homologySheaf_exact₁ T n₀ n₁ hT h)
  exact hExact

end SpecCohomology

end WeilComplex

end AlgebraicGeometry
