/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.LisseLocus
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseNilInvariance
public import WeilConjectures.WeilSheaf.LisseLocus

/-!
# A lisse locus of small codimension for a constructible `ℓ`-adic sheaf

Let `X` be a nonempty scheme of finite type over a field `k` and `F` a constructible
`ℓ`-adic sheaf on the pro-étale site of `X`. Then `F` is lisse on an open subscheme `U` whose
complement has strictly smaller dimension than `X`
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.exists_open_topologicalKrullDim_compl_lt`,
the pro-étale clause of blueprint `proposition-purity-lisse-part-fourier-transform`).

The lisse locus `L` of `F` (the union of all opens on which `F` is lisse) is open, `F` is lisse
on it by Zariski locality of lissity, and it contains every generic point of an irreducible
component, hence is dense
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.exists_opens_isAdicLisseSheaf'`, which
rests on the nil-invariance of lissity
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_adicUpperStar_of_surjective`). The complement
of a dense open has smaller dimension (`topologicalKrullDim_compl_lt_of_dense`).

## Main statements

- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.exists_dense_isAdicLisseSheaf`
- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.exists_open_topologicalKrullDim_compl_lt`
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- **Generic lissity on a dense open.** On a scheme whose underlying space is Noetherian, a
constructible `ℓ`-adic sheaf is lisse on a dense open subscheme: its lisse locus, the union of
all opens on which it is lisse, is open, the sheaf is lisse on it by Zariski locality of lissity,
and it contains every generic point of an irreducible component. -/
theorem IsAdicConstructibleSheaf.exists_dense_isAdicLisseSheaf
    [TopologicalSpace.NoetherianSpace X] {F : AdicSheaf l X} (hF : IsAdicConstructibleSheaf F) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsAdicLisseSheaf ((U.ι)^*ᵃ[l].obj F) := by
  set L : Set X := {x | ∃ W : X.Opens, x ∈ W ∧ IsAdicLisseSheaf ((W.ι)^*ᵃ[l].obj F)}
  have hL : IsOpen L := isOpen_iff_forall_mem_open.2 fun x ⟨W, hxW, hW⟩ ↦
    ⟨W, fun y hy ↦ ⟨W, hy, hW⟩, W.isOpen, hxW⟩
  refine ⟨⟨L, hL⟩, dense_of_genericPoints_subset fun η hη ↦
    hF.exists_opens_isAdicLisseSheaf' hη, ?_⟩
  set U : X.Opens := ⟨L, hL⟩
  refine IsAdicLisseSheaf.of_forall_exists_opens fun y ↦ ?_
  obtain ⟨W, hyW, hW⟩ := y.2
  refine ⟨U.ι ⁻¹ᵁ W, hyW, ?_⟩
  have h₁ := hW.upperStar (U.ι ∣_ W)
  have h₂ : IsAdicLisseSheaf ((U.ι ∣_ W ≫ W.ι)^*ᵃ[l].obj F) :=
    h₁.of_iso ((adicUpperStarComp l (U.ι ∣_ W) W.ι).app F).symm
  have h₃ : IsAdicLisseSheaf (((U.ι ⁻¹ᵁ W).ι ≫ U.ι)^*ᵃ[l].obj F) :=
    h₂.of_iso ((adicUpperStarCongr l (morphismRestrict_ι U.ι W)).app F)
  exact h₃.of_iso ((adicUpperStarComp l (U.ι ⁻¹ᵁ W).ι U.ι).app F)

/-- Blueprint `proposition-purity-lisse-part-fourier-transform` (2): A lisse locus for a
constructible `ℓ`-adic sheaf.

Let `X` be a nonempty scheme of finite type over a field `k` and `F` a constructible `ℓ`-adic
sheaf on `X_proet`. Then there is an open subscheme `U ⊆ X` with `dim (X \ U) < dim X` on which
the restriction `F|_U` is lisse.

(For `X` empty both dimensions are `⊥` and the strict inequality cannot hold, which is why `X`
is assumed nonempty.)

The proof takes the dense lisse locus of `IsAdicConstructibleSheaf.exists_dense_isAdicLisseSheaf`
and uses that the complement of a dense open in the Noetherian space `X`, of finite dimension,
has smaller dimension (`topologicalKrullDim_compl_lt_of_dense`). -/
theorem IsAdicConstructibleSheaf.exists_open_topologicalKrullDim_compl_lt {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [Nonempty X]
    {F : AdicSheaf l X} (hF : IsAdicConstructibleSheaf F) :
    ∃ U : X.Opens, topologicalKrullDim ((U : Set X)ᶜ : Set X) < topologicalKrullDim X ∧
      IsAdicLisseSheaf ((U.ι)^*ᵃ[l].obj F) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  obtain ⟨U, hU, hF⟩ := hF.exists_dense_isAdicLisseSheaf
  exact ⟨U, topologicalKrullDim_compl_lt_of_dense (topologicalKrullDim_ne_top_of_compactSpace f)
    hU U.isOpen, hF⟩

end ProEtale

end AlgebraicGeometry
