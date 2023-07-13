#!/bin/bash

set -e

# Directory name for the artifact:
ARTIFACT_DIR="the_artifact"

# Arguments: user, project, hash, output_dir_name.
get_gitlab_archive () {
  wget "https://gitlab.mpi-sws.org/$1/$2/-/archive/$3/$2-$3.tar.gz"
  tar xf "$2-$3.tar.gz" --transform "s/^$2-$3/$4/"
  rm "$2-$3.tar.gz"
}

# Arguments: user, project, hash, output_dir_name.
get_github_archive () {
  wget -q "https://github.com/$1/$2/archive/$3.zip"
  unzip -q "$3.zip"
  mv "$2-$3" "$4"
  rm "$3.zip"
}

get_github_archive_by_tag () {
  wget -q "https://github.com/$1/$2/archive/refs/tags/$3.zip"
  unzip -q "$3.zip"
  mv "$2-$3" "$4"
  rm "$3.zip"
}

get_github_tag_commit_hash () {
  curl https://api.github.com/repos/$1/$2/tags | jq -r ".[] | select(.name==\"$3\") .commit.sha"
}

# Archives for private repos
# Arguments: user, project, hash, output_dir_name.
get_local_archive () {
  if [[ -f "../resources/$2-$3.tar.gz" ]]; then
      cp "../resources/$2-$3.tar.gz" .
      tar xf "$2-$3.tar.gz" --transform "s/^$2-$3/$4/"
      rm "$2-$3.tar.gz"
  else
      echo "Please download https://gitlab.mpi-sws.org/$1/$2/-/archive/$3/$2-$3.tar.gz to resources/$2-$3.tar.gz"
      exit 1
  fi
}

# Deleting previously generated artifact and creating new directory.
rm -rf ${ARTIFACT_DIR} ${ARTIFACT_DIR}.tgz ${ARTIFACT_DIR}.zip
mkdir ${ARTIFACT_DIR}

#                      DON'T MODIFY THE CODE ABOVE!                            #
################################################################################

# The logic for creating the artifact goes here:

# Commit hashes (projects from GitLab):
STDPP_HASH="0231fed2d94280c383be3bb0b1c3eafecdde0fe1"
IRIS_HASH="d6e890ee978b27893eb1bac1f50d766441570180"
TRANSFINITE_HASH="aa492e2ce211c55392147498b0dcadcf5ea93457"
MELOCOTON_TAG="artifact-oopsla23"
AUTOSUBST_HASH="495d547fa2a3e40da0f7d2a31469ac8caab058d2"


# Downloading the sources for everything.
cd ${ARTIFACT_DIR}
get_gitlab_archive iris stdpp            ${STDPP_HASH}    coq-stdpp
get_gitlab_archive simonspies iris-parametric-index ${IRIS_HASH} iris-parametric-index
get_gitlab_archive simonspies transfinite-parametric-stepindex ${TRANSFINITE_HASH} transfinite-parametric-stepindex
get_github_archive_by_tag logsem melocoton ${MELOCOTON_TAG} melocoton
get_github_archive coq-community autosubst ${AUTOSUBST_HASH} autosubst
# ugly hack
sed -i s/8.16/8.17/g autosubst/coq-autosubst.opam
cd ..

# Writing generation data (commit hashes and the likes).
GENDATA=${ARTIFACT_DIR}/generation_data.txt
echo "Generation data for the artifact"           >  ${GENDATA}
echo "================================"           >> ${GENDATA}
echo "iris/stdpp.git    : ${STDPP_HASH}"          >> ${GENDATA}
echo "simonspies/iris-parametric-index.git    : ${IRIS_HASH}"          >> ${GENDATA}
echo "simonspies/transfinite-parametric-stepindex.git    : ${TRANSFINITE_HASH}"          >> ${GENDATA}
echo "logsem/melocoton.git    : $(get_github_tag_commit_hash logsem melocoton $MELOCOTON_TAG)"          >> ${GENDATA}
echo "coq-community/autosubst.git    : ${AUTOSUBST_HASH}"          >> ${GENDATA}
# Copying static files.
cp resources/README.md ${ARTIFACT_DIR}/

################################################################################
#                      DON'T MODIFY THE CODE BELOW!                            #

# Copying script for building the artifact.
cp resources/build_artifact.sh ${ARTIFACT_DIR}/

# Packaging the artifact.
tar czf ${ARTIFACT_DIR}.tgz --owner=anon --group=anon ${ARTIFACT_DIR}
zip -q -r ${ARTIFACT_DIR}.zip ${ARTIFACT_DIR}

# Final message.
echo -e "Artifact created as file [\e[32m${ARTIFACT_DIR}.tgz\e[0m]."
echo -e "And also as file [\e[32m${ARTIFACT_DIR}.zip\e[0m]."
echo -e "Browse folder [\e[32m${ARTIFACT_DIR}\e[0m] to check its contents."
