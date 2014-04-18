#version 330 core
 
//Sampler defaults to unit 0 which is where our texture is bound
uniform sampler2D tex;
 
in vec2 fuv;
 
out vec4 color;
 
void main(void){
  color = texture(tex, fuv);
}
