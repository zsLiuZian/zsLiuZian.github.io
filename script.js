// 获取所有导航链接
const navLinks = document.querySelectorAll('.nav-link');

// 创建一个观察者来监测每个部分的可见性
const observer = new IntersectionObserver((entries) => {
  entries.forEach(entry => {
    const id = entry.target.id;
    const navLink = document.querySelector(`.nav-link[href="#${id}"]`);

    if (entry.isIntersecting) {
      // 如果 section 进入视口，激活对应的导航链接
      navLink.classList.add('active');
    } else {
      // 如果 section 离开视口，移除高亮
      navLink.classList.remove('active');
    }
  });
}, {
  threshold: 0.5, // 当 50% 的 section 可见时触发
});

// 观察所有需要监测的 section
document.querySelectorAll('section').forEach(section => {
  observer.observe(section);
});
