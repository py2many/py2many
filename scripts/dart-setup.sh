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
if ! grep vnum pubspec.yaml ; then
  cat pubspec.yaml
  sed -i.bak '/test:/d' pubspec.yaml
  # Force version downgrade here
  sed -i.bak 's:1.16.0:1.15.0:' pubspec.yaml
  flutter pub add vnum
fi
