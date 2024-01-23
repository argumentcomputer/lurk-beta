use crate::circuit::gadgets::circom::CircomGadgetReference;
use thiserror::Error;

/// Enum related to error happening while dealing with the Circom Coprocessor.
#[derive(Error, Debug)]
pub enum CircomCoprocessorError {
    /// Error if we could not find the specified gadget either locally or on Github.
    #[error("
{prelude}: no circom gadget with reference `{reference}` found locally or on Github. Make sure that the reference
is properly formatted as `<AUTHOR>/<NAME>`.

If you want to setup a new circom gadget `{reference}`, place your circom files in a designated folder and
create a file called `{name}.circom`. The circom binary expects `<{name}_FOLDER>/{name}.circom`
as the input file; in this file you must declare your circom main component.

Then run `lurk coprocessor --reference {reference} <{name}_FOLDER>` to instantiate a new gadget with reference `{reference}`.")]
    GadgetNotFound {
        prelude: String,
        reference: CircomGadgetReference,
        name: String,
    },
    /// Error if we could not find the specified gadget  locally and no release version is specified
    /// for Github while we have checked that the desired gadget exists.
    #[error("
{prelude}: no circom gadget with reference `{reference}` found locally. A repository with the given reference
was found:

https://github.com/{reference}

However, the gadget has no version specified. Please provide a correct release tag and retry.")]
    MissingGadgetVersion { prelude: String, reference: String },
    /// Error if we wanted to initiate a  remote HTTP call but encountered an error.
    #[error(
        "
{prelude}: no circom gadget with reference `{reference}` found locally. We tried to look for it on 
Github but we encountered an error:

{source}

Please retry."
    )]
    RemoteCallFailure {
        prelude: String,
        reference: CircomGadgetReference,
        #[source]
        source: Box<dyn std::error::Error + Sync + Send>,
    },
    /// Error if we try to create the directories for the gadget on the file system but failed.
    #[error(
    "
{prelude}: we tried to create the necessary assets for the gadget on the file system but we encountered
 an error:

{source}

Please retry."
    )]
    AssetCreationFailure {
        prelude: String,
        reference: CircomGadgetReference,
        #[source]
        source: Box<dyn std::error::Error + Sync + Send>,
    },
    /// Error when we got a satic file from Github but could not process it.
    #[error("
{prelude}: no circom gadget with reference `{reference}` found locally. We tried to download the resource
at {asset_url}, but encountered an error:

{source}

Please make sure that the resource corresponds to a valid r1cs or wasm file and retry.")]
    PayloadProcessingError {
        prelude: String,
        reference: CircomGadgetReference,
        #[source]
        source: Box<dyn std::error::Error + Sync + Send>,
        asset_url: String,
    },
}
