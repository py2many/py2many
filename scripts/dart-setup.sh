dart --version
flutter --version
set -ex

# tests/build here must be the same as defined in test_cli
if [[ ! -f tests/build/pubspec.yaml ]]; then
  dart create --no-pub --force -t package-simple tests/build
  cat tests/build/pubspec.yaml
fi

cd tests/build
if ! grep collection pubspec.yaml ; then
  # Specifying the version here doesnt stick
  dart pub add collection:1.15.0
  cat pubspec.yaml
  dart pub add sprintf
  dart pub add tuple
fi
